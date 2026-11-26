-- Prove2me | solution 1 for dense_range_one_sub_cayleyTransform
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:53:16.735036+00:00
-- url     : https://prove2.me/submissions/0ef07fed-2548-4209-807e-cddd42bd41b5

import Definitions.Def_Spectral_Cayley_Basic
import Definitions.Def_Spectral_Cayley_Unitary
import Theorems.Thm_cayleyTransform_apply_plus


set_option autoImplicit false
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
theorem _root_.solution
    (A : E →ₗ.[ℂ] E) (hA : IsSelfAdjoint A) :
    DenseRange (fun x => x - cayleyTransform A hA x) := by
  apply hA.dense_domain.mono
  intro z hz
  let x : A.domain := ⟨z, hz⟩
  have hgap :
      (A x + Complex.I • (x : E)) - (A x - Complex.I • (x : E)) =
        ((2 : ℂ) * Complex.I) • (x : E) := by
    module
  have htwoI : (2 : ℂ) * Complex.I ≠ 0 :=
    mul_ne_zero (by norm_num) Complex.I_ne_zero
  refine ⟨(((2 : ℂ) * Complex.I)⁻¹) • (A x + Complex.I • (x : E)), ?_⟩
  calc
    ((2 * Complex.I)⁻¹ : ℂ) • (A x + Complex.I • (x : E)) -
          cayleyTransform A hA
            (((2 * Complex.I)⁻¹ : ℂ) • (A x + Complex.I • (x : E))) =
        ((2 * Complex.I)⁻¹ : ℂ) • (A x + Complex.I • (x : E)) -
          ((2 * Complex.I)⁻¹ : ℂ) •
            cayleyTransform A hA (A x + Complex.I • (x : E)) := by
              rw [map_smul]
    _ = ((2 * Complex.I)⁻¹ : ℂ) • (A x + Complex.I • (x : E)) -
          ((2 * Complex.I)⁻¹ : ℂ) • (A x - Complex.I • (x : E)) := by
            rw [cayleyTransform_apply_plus A hA x]
    _ = ((2 * Complex.I)⁻¹ : ℂ) •
          ((A x + Complex.I • (x : E)) - (A x - Complex.I • (x : E))) := by
            exact (smul_sub _ _ _).symm
    _ = ((2 * Complex.I)⁻¹ : ℂ) • (((2 : ℂ) * Complex.I) • (x : E)) := by
          rw [hgap]
    _ = (x : E) := by
          rw [smul_smul, inv_mul_cancel₀ htwoI, one_smul]
    _ = z := rfl
