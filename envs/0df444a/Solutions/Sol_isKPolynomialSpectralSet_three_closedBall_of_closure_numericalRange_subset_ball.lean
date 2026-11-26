-- Prove2me | solution 1 for isKPolynomialSpectralSet_three_closedBall_of_closure_numericalRange_subset_ball
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:28:09.45935+00:00
-- url     : https://prove2.me/submissions/86b2ce04-5207-4da2-a970-5dc58f983b06

import Definitions.Def_Operator_Crouzeix_SpectralCauchy
import Definitions.Def_Operator_Crouzeix_SpectralAuxiliary
import Definitions.Def_Operator_Crouzeix_AffineAuxiliary
import Definitions.Def_Operator_Crouzeix_ApproximationSupNorm
import Definitions.Def_Operator_Crouzeix_SpectralAuxiliaryCenter
import Theorems.Thm_norm_aeval_le_three_mul_polynomialSupNorm_closedBall_of_closure_numericalRange_subset_ball
import Theorems.Thm_spectrum_subset_closure_numericalRange


set_option autoImplicit false
open Complex Polynomial spectrum Filter Topology
open scoped InnerProductSpace Pointwise
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
theorem _root_.solution
    (A : E →L[ℂ] E) {c : ℂ} {r : ℝ} (hr : 0 < r)
    (hW : closure (numericalRange A) ⊆ Metric.ball c r) :
    IsKPolynomialSpectralSet A 3 (Metric.closedBall c r) :=
  ⟨((spectrum_subset_closure_numericalRange A).trans hW).trans Metric.ball_subset_closedBall,
    fun p => norm_aeval_le_three_mul_polynomialSupNorm_closedBall_of_closure_numericalRange_subset_ball
      A hr hW p⟩
