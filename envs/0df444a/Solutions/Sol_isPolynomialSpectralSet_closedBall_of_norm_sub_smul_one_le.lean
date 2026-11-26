-- Prove2me | solution 1 for isPolynomialSpectralSet_closedBall_of_norm_sub_smul_one_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:27:10.743923+00:00
-- url     : https://prove2.me/submissions/070febbc-a4d1-4794-a134-ff84bd437ad8

import Mathlib.Analysis.Normed.Module.Ball.Pointwise
import Definitions.Def_Operator_Crouzeix_AffinePolynomial
import Definitions.Def_Operator_Crouzeix_VonNeumann
import Definitions.Def_Operator_SpectralSet_SpectrumInNR
import Definitions.Def_Operator_Crouzeix_AffineDisk
import Theorems.Thm_closure_numericalRange_subset_closedBall_of_norm_sub_smul_one_le
import Theorems.Thm_norm_aeval_le_polynomialSupNorm_closedBall_of_norm_sub_smul_one_le
import Theorems.Thm_spectrum_subset_closure_numericalRange


set_option autoImplicit false
open scoped InnerProductSpace Pointwise Polynomial
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [CompleteSpace E]
theorem _root_.solution
    (A : E →L[ℂ] E) (c : ℂ) {R : ℝ} (hR : 0 < R)
    (hA : ‖A - c • 1‖ ≤ R) :
    IsPolynomialSpectralSet A (Metric.closedBall c R) := by
  constructor
  · exact (spectrum_subset_closure_numericalRange A).trans
      (closure_numericalRange_subset_closedBall_of_norm_sub_smul_one_le A c hA)
  · intro p
    rw [one_mul]
    exact norm_aeval_le_polynomialSupNorm_closedBall_of_norm_sub_smul_one_le A c hR hA p
