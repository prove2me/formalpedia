-- Prove2me | solution 1 for norm_add_star_le_two_mul_of_doubleLayer_representation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:37:53.634015+00:00
-- url     : https://prove2.me/submissions/bfbf9a84-08a3-4d1f-ab85-57944350988c

import Definitions.Def_Operator_Crouzeix_DoubleLayerBound
import Definitions.Def_Operator_Crouzeix_SymmetrizedBound
import Theorems.Thm_norm_inv_two_pi_smul_intervalIntegral_le_two_mul_of_nonneg


set_option autoImplicit false
open MeasureTheory
open scoped InnerProductSpace Interval Real
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
theorem _root_.solution
    (F G : E →L[ℂ] E) {K : ℝ → E →L[ℂ] E} {f : ℝ → ℂ} {M : ℝ}
    (hrepresentation : F + star G =
      (2 * Real.pi)⁻¹ • (∫ t in (0 : ℝ)..(2 * Real.pi), f t • K t))
    (hK : IntervalIntegrable K volume 0 (2 * Real.pi))
    (hfK : IntervalIntegrable (fun t ↦ f t • K t) volume 0 (2 * Real.pi))
    (hpos : ∀ t ∈ Set.Ioc (0 : ℝ) (2 * Real.pi), 0 ≤ K t)
    (hnorm : ∫ t in (0 : ℝ)..(2 * Real.pi), K t =
      (4 * Real.pi) • (1 : E →L[ℂ] E))
    (hM : 0 ≤ M) (hf : ∀ t ∈ Set.Ioc (0 : ℝ) (2 * Real.pi), ‖f t‖ ≤ M) :
    ‖F + star G‖ ≤ 2 * M := by
  rw [hrepresentation]
  exact norm_inv_two_pi_smul_intervalIntegral_le_two_mul_of_nonneg
    hK hfK hpos hnorm hM hf
