-- Prove2me | solution 1 for norm_aeval_mul_crouzeixPolynomialAuxiliaryOperator_ball_center_le_of_isStarNormal_aeval
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:38:42.593246+00:00
-- url     : https://prove2.me/submissions/04c9146d-121d-4d4f-84a0-61e7586bfbfd

import Definitions.Def_Operator_Crouzeix_AffineAuxiliary
import Definitions.Def_Operator_NumericalRange_Bounded
import Definitions.Def_Operator_SpectralSet_Normal
import Definitions.Def_Operator_SpectralSet_SpectrumInNR
import Definitions.Def_Operator_Crouzeix_NormalProduct
import Theorems.Thm_bddAbove_norm_eval_image_of_isCompact
import Theorems.Thm_crouzeixPolynomialAuxiliaryOperator_ball_center_eq_eval_center_smul_one
import Theorems.Thm_isBounded_numericalRange
import Theorems.Thm_norm_aeval_le_polynomialSupNorm_of_isStarNormal_aeval
import Theorems.Thm_norm_eval_le_polynomialSupNorm
import Theorems.Thm_spectrum_subset_closure_numericalRange


set_option autoImplicit false
open Complex Polynomial Set
open scoped InnerProductSpace
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
theorem _root_.solution
    (A : E →L[ℂ] E) (c : ℂ) {R : ℝ}
    (hA : ‖A - c • (1 : E →L[ℂ] E)‖ < R)
    (hc : c ∈ closure (numericalRange A)) (p : Polynomial ℂ)
    [IsStarNormal (Polynomial.aeval A p)] :
    ‖Polynomial.aeval A p *
        crouzeixPolynomialAuxiliaryOperator A
          (SmoothJordanDomain.ball c R
            ((norm_nonneg (A - c • 1)).trans_lt hA)) p‖ ≤
      polynomialSupNorm p (closure (numericalRange A)) ^ 2 := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · let _ := hE
    have hzero : Polynomial.aeval A p *
        crouzeixPolynomialAuxiliaryOperator A
          (SmoothJordanDomain.ball c R
            ((norm_nonneg (A - c • 1)).trans_lt hA)) p = 0 :=
      Subsingleton.elim _ _
    rw [hzero, norm_zero]
    exact sq_nonneg _
  let _ := hE
  let m := polynomialSupNorm p (closure (numericalRange A))
  have hcompact : IsCompact (closure (numericalRange A)) :=
    (isBounded_numericalRange A).isCompact_closure
  have hpA : ‖Polynomial.aeval A p‖ ≤ m :=
    norm_aeval_le_polynomialSupNorm_of_isStarNormal_aeval A hcompact
      (spectrum_subset_closure_numericalRange A) p
  have hpc : ‖Polynomial.eval c p‖ ≤ m :=
    norm_eval_le_polynomialSupNorm p
      (bddAbove_norm_eval_image_of_isCompact p hcompact) hc
  rw [crouzeixPolynomialAuxiliaryOperator_ball_center_eq_eval_center_smul_one
    A c hA p]
  calc
    ‖Polynomial.aeval A p *
        (star (Polynomial.eval c p) • (1 : E →L[ℂ] E))‖ ≤
        ‖Polynomial.aeval A p‖ *
          ‖star (Polynomial.eval c p) • (1 : E →L[ℂ] E)‖ :=
      norm_mul_le _ _
    _ = ‖Polynomial.aeval A p‖ * ‖Polynomial.eval c p‖ := by
      rw [norm_smul, norm_star, norm_one, mul_one]
    _ ≤ m * m :=
      mul_le_mul hpA hpc (norm_nonneg _)
        ((norm_nonneg _).trans hpA)
    _ = polynomialSupNorm p (closure (numericalRange A)) ^ 2 := by
      rw [pow_two]
