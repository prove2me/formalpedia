-- Prove2me | solution 1 for norm_aeval_le_three_mul_polynomialSupNorm_closedBall_of_closure_numericalRange_subset_ball
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:54:43.851082+00:00
-- url     : https://prove2.me/submissions/57bdde07-54b6-445b-b1a4-48741f9377c6

import Definitions.Def_Operator_Crouzeix_SpectralCauchy
import Definitions.Def_Operator_Crouzeix_SpectralAuxiliary
import Definitions.Def_Operator_Crouzeix_AffineAuxiliary
import Definitions.Def_Operator_Crouzeix_ApproximationSupNorm
import Definitions.Def_Operator_Crouzeix_SpectralAuxiliaryCenter
import Theorems.Thm_norm_aeval_add_eval_center_smul_one_le_of_closure_numericalRange_subset_ball
import Theorems.Thm_bddAbove_norm_eval_image_of_isCompact
import Theorems.Thm_norm_eval_le_polynomialSupNorm


set_option autoImplicit false
open Complex Polynomial spectrum Filter Topology
open scoped InnerProductSpace Pointwise
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
theorem _root_.solution
    (A : E →L[ℂ] E) {c : ℂ} {r : ℝ} (hr : 0 < r)
    (hW : closure (numericalRange A) ⊆ Metric.ball c r) (p : ℂ[X]) :
    ‖aeval A p‖ ≤ 3 * polynomialSupNorm p (Metric.closedBall c r) := by
  have hsym := norm_aeval_add_eval_center_smul_one_le_of_closure_numericalRange_subset_ball
    A hr hW p
  have hc : ‖p.eval c‖ ≤ polynomialSupNorm p (Metric.closedBall c r) :=
    norm_eval_le_polynomialSupNorm p
      (bddAbove_norm_eval_image_of_isCompact p (isCompact_closedBall c r))
      (Metric.mem_closedBall_self hr.le)
  have hconst : ‖(p.eval c) • (1 : E →L[ℂ] E)‖ ≤ ‖p.eval c‖ := by
    rw [norm_smul]
    exact mul_le_of_le_one_right (norm_nonneg _) ContinuousLinearMap.norm_id_le
  calc ‖aeval A p‖ = ‖(aeval A p + (p.eval c) • (1 : E →L[ℂ] E)) - (p.eval c) • (1 : E →L[ℂ] E)‖ := by
        rw [add_sub_cancel_right]
    _ ≤ ‖aeval A p + (p.eval c) • (1 : E →L[ℂ] E)‖ + ‖(p.eval c) • (1 : E →L[ℂ] E)‖ :=
        norm_sub_le _ _
    _ ≤ 2 * polynomialSupNorm p (Metric.closedBall c r) +
          polynomialSupNorm p (Metric.closedBall c r) := add_le_add hsym (hconst.trans hc)
    _ = 3 * polynomialSupNorm p (Metric.closedBall c r) := by ring
