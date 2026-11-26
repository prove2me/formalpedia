-- Prove2me | solution 1 for norm_aeval_add_star_crouzeixPolynomialAuxiliaryOperator_ball_le_of_closure_numericalRange_subset_ball
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:50:07.512457+00:00
-- url     : https://prove2.me/submissions/830ba197-7e05-429a-a71b-1a65dec79834

import Mathlib.Analysis.Complex.CauchyIntegral
import Definitions.Def_Operator_Crouzeix_CircleCauchy
import Definitions.Def_Operator_Crouzeix_CircleSymmetrized
import Definitions.Def_Operator_Crouzeix_AffinePolynomial
import Definitions.Def_Operator_Crouzeix_SpectralCauchy
import Theorems.Thm_normalized_circleIntegral_eval_smul_resolvent_eq_aeval_of_spectrum_subset_ball
import Theorems.Thm_circleIntegral_resolvent_eq_two_pi_I_smul_one_of_spectrum_subset_ball
import Theorems.Thm_aeval_add_star_crouzeixPolynomialAuxiliaryOperator_eq_doubleLayerIntegral_of_cauchy
import Theorems.Thm_norm_aeval_add_star_le_two_mul_polynomialSupNorm_of_representation
import Theorems.Thm_spectrum_subset_closure_numericalRange


set_option autoImplicit false
open Complex Polynomial spectrum
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
theorem _root_.solution
    (A : E →L[ℂ] E) {r : ℝ} (hr : 0 < r)
    (hW : closure (numericalRange A) ⊆ Metric.ball (0 : ℂ) r) (p : ℂ[X]) :
    ‖aeval A p + star (crouzeixPolynomialAuxiliaryOperator A
        (SmoothJordanDomain.ball 0 r hr) p)‖ ≤
      2 * polynomialSupNorm p (Metric.closedBall (0 : ℂ) r) := by
  have hσ : spectrum ℂ A ⊆ Metric.ball (0 : ℂ) r :=
    (spectrum_subset_closure_numericalRange A).trans hW
  have hOmega : closure (numericalRange A) ⊆ (SmoothJordanDomain.ball 0 r hr).carrier := hW
  have hCauchy : aeval A p = (2 * (Real.pi : ℂ) * I)⁻¹ •
      contourIntegral (fun z => Polynomial.eval z p • resolvent A z)
        (SmoothJordanDomain.ball 0 r hr).boundaryParam :=
    (normalized_circleIntegral_eval_smul_resolvent_eq_aeval_of_spectrum_subset_ball A hr hσ p).symm
  have hrep := aeval_add_star_crouzeixPolynomialAuxiliaryOperator_eq_doubleLayerIntegral_of_cauchy
    A (SmoothJordanDomain.ball 0 r hr) p hOmega hCauchy
  exact norm_aeval_add_star_le_two_mul_polynomialSupNorm_of_representation A hr.le hW p _ hrep
    (circleIntegral_resolvent_eq_two_pi_I_smul_one_of_spectrum_subset_ball A hr hσ)
