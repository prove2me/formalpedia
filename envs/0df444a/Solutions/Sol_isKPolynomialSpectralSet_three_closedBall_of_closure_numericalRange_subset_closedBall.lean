-- Prove2me | solution 1 for isKPolynomialSpectralSet_three_closedBall_of_closure_numericalRange_subset_closedBall
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:28:17.788659+00:00
-- url     : https://prove2.me/submissions/75d2d198-96bb-4658-b364-afd24ebd6ecc

import Definitions.Def_Operator_Crouzeix_SpectralCauchy
import Definitions.Def_Operator_Crouzeix_SpectralAuxiliary
import Definitions.Def_Operator_Crouzeix_AffineAuxiliary
import Definitions.Def_Operator_Crouzeix_ApproximationSupNorm
import Definitions.Def_Operator_Crouzeix_SpectralAuxiliaryCenter
import Theorems.Thm_norm_aeval_le_three_mul_polynomialSupNorm_closedBall_of_closure_numericalRange_subset_closedBall
import Theorems.Thm_spectrum_subset_closure_numericalRange


set_option autoImplicit false
open Complex Polynomial spectrum Filter Topology
open scoped InnerProductSpace Pointwise
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
theorem _root_.solution
    (A : E →L[ℂ] E) {c : ℂ} {r : ℝ} (hr : 0 ≤ r)
    (hW : closure (numericalRange A) ⊆ Metric.closedBall c r) :
    IsKPolynomialSpectralSet A 3 (Metric.closedBall c r) :=
  ⟨(spectrum_subset_closure_numericalRange A).trans hW,
    fun p => norm_aeval_le_three_mul_polynomialSupNorm_closedBall_of_closure_numericalRange_subset_closedBall
      A hr hW p⟩
