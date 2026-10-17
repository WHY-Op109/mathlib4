import Mathlib.LinearAlgebra.WeylAlgebra.Basic
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Data.ZMod.Basic

/-!
# Tests for `WeylAlgebra`

The universal property is exercised by building the one-variable canonical commutation
representation on `R[X]`. Degenerate forms show that nontriviality of `WeylAlgebra B` and
injectivity of `WeylAlgebra.ι B` depend on `B`.
-/

open Polynomial WeylAlgebra

namespace WeylAlgebraTest

variable {R : Type*} [CommRing R]

/-- The standard symplectic form `B (a, b) (c, d) = a * d - b * c` on `R × R`. -/
def stdForm : LinearMap.BilinForm R (R × R) :=
  LinearMap.mk₂ R (fun p q => p.1 * q.2 - p.2 * q.1)
    (fun _ _ _ => by simp; ring) (fun _ _ _ => by simp; ring)
    (fun _ _ _ => by simp; ring) (fun _ _ _ => by simp; ring)

@[simp] lemma stdForm_apply (p q : R × R) : stdForm p q = p.1 * q.2 - p.2 * q.1 := rfl

/-- `(a, b) ↦ a • ∂ + b • X`, acting on `R[X]`. -/
noncomputable def ccr : R × R →ₗ[R] Module.End R R[X] :=
  (LinearMap.fst R R R).smulRight (derivative : Module.End R R[X]) +
    (LinearMap.snd R R R).smulRight (LinearMap.mulLeft R (X : R[X]))

lemma ccr_apply (p : R × R) (f : R[X]) : ccr p f = p.1 • derivative f + p.2 • (X * f) := rfl

lemma ccr_cond (p q : R × R) :
    ccr p * ccr q = ccr q * ccr p + algebraMap R _ (stdForm p q) := by
  refine LinearMap.ext fun f => ?_
  simp [ccr_apply, Module.End.mul_apply, derivative_mul, smul_add, smul_smul]
  simp only [smul_eq_C_mul, C_mul]
  ring

/-- The one-variable canonical commutation representation on `R[X]`, built with `lift`. -/
noncomputable def ccrRep : WeylAlgebra (stdForm (R := R)) →ₐ[R] Module.End R R[X] :=
  lift (stdForm (R := R)) ⟨ccr, ccr_cond⟩

@[simp] lemma ccrRep_ι (p : R × R) : ccrRep (ι stdForm p) = ccr p := lift_ι_apply _ _ _

example : ccrRep (ι stdForm ((1 : R), (0 : R))) (X ^ 2) = 2 * X := by
  simp [ccr_apply]
  ring

example : ccrRep (ι stdForm ((0 : R), (1 : R))) 1 = X := by
  simp [ccr_apply]

/-- `ι_lie_ι` evaluates the commutator of generators to `algebraMap R _ (stdForm (1, 0) (0, 1))`,
that is `1`. `ccrRep` sends these generators to `∂` and `X`: this is `⁅∂, X⁆ = 1`. -/
example : ⁅ι stdForm ((1 : R), (0 : R)), ι stdForm ((0 : R), (1 : R))⁆ = 1 := by
  simp

/-- For the standard symplectic form, `ι` is injective over every commutative ring, including
in characteristic `2`; the representation witnesses this. -/
theorem ι_stdForm_injective : Function.Injective (ι (stdForm (R := R))) := by
  refine (injective_iff_map_eq_zero _).2 fun p hp => ?_
  have h1 := congr_arg (fun a => (ccrRep a 1).coeff 1) hp
  have h2 := congr_arg (fun a => (ccrRep a X).coeff 0) hp
  simp [ccr_apply] at h1 h2
  exact Prod.ext h2 h1

/-- Nontriviality is a property of specific forms, here obtained from the representation. -/
example [Nontrivial R] : Nontrivial (WeylAlgebra (stdForm (R := R))) :=
  ccrRep.toRingHom.domain_nontrivial

/-- In characteristic `2` the standard form is alternating, and nothing degenerates. -/
example : Function.Injective (ι (stdForm (R := ZMod 2))) := ι_stdForm_injective

/-- In characteristic `2`, `B x y = x * y` is skew-symmetric ... -/
example : ∀ x y : ZMod 2, LinearMap.mul (ZMod 2) (ZMod 2) x y =
    -LinearMap.mul (ZMod 2) (ZMod 2) y x := by
  decide

/-- ... but not alternating, and its Weyl algebra is the zero ring. -/
example : Subsingleton (WeylAlgebra (LinearMap.mul (ZMod 2) (ZMod 2))) :=
  subsingleton_of_isUnit_apply_self (m := 1) (by simp)

/-- The form `B x y = 2 * x * y` on `ℤ`. -/
def twoMul : LinearMap.BilinForm ℤ ℤ := (2 : ℤ) • LinearMap.mul ℤ ℤ

@[simp] lemma twoMul_apply (x y : ℤ) : twoMul x y = 2 * (x * y) := rfl

/-- `WeylAlgebra twoMul` is nonzero, as it maps to `(ZMod 2)[X]`... -/
example : Nontrivial (WeylAlgebra twoMul) :=
  (lift twoMul (A := (ZMod 2)[X])
    ⟨LinearMap.toSpanSingleton ℤ _ X, fun m n => by
      simp [mul_comm, mul_left_comm, CharTwo.two_eq_zero]⟩).toRingHom.domain_nontrivial

/-- ... yet `ι` is not injective: `twoMul 1 1 = 2` in `ℤ`, and the image of `2` in the Weyl
algebra vanishes, so `ι 2 = 0`. -/
example : ¬Function.Injective (ι twoMul) := by
  intro h
  have h2 : algebraMap ℤ (WeylAlgebra twoMul) 2 = 0 := by
    simpa using algebraMap_apply_self twoMul 1
  have : ι twoMul 2 = algebraMap ℤ _ 2 * ι twoMul 1 := by
    rw [← Algebra.smul_def, ← map_smul, smul_eq_mul, mul_one]
  rw [h2, zero_mul] at this
  exact two_ne_zero (h (this.trans (map_zero _).symm))

/-- `ext` uses `WeylAlgebra.hom_ext` rather than the ext lemma of the underlying quotient. -/
example {M : Type*} [AddCommGroup M] [Module R M] (B : LinearMap.BilinForm R M)
    {A : Type*} [Semiring A] [Algebra R A] (f g : WeylAlgebra B →ₐ[R] A)
    (h : ∀ m, f (ι B m) = g (ι B m)) : f = g := by
  ext m
  guard_hyp m : M
  exact h m

end WeylAlgebraTest
