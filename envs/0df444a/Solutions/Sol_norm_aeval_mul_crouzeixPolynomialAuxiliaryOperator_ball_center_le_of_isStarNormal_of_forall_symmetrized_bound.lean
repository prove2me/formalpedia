-- Prove2me | solution 1 for norm_aeval_mul_crouzeixPolynomialAuxiliaryOperator_ball_center_le_of_isStarNormal_of_forall_symmetrized_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:34:15.820913+00:00
-- url     : https://prove2.me/submissions/63511b87-2453-4621-87aa-140ceeddbe32

import Definitions.Def_Operator_Crouzeix_ConvexRunge
import Definitions.Def_Operator_Crouzeix_NormalProduct
import Definitions.Def_Operator_Crouzeix_SmoothSupportDomain
import Definitions.Def_Operator_NumericalRange_Convex
import Definitions.Def_Operator_NumericalRange_Nonempty
import Definitions.Def_Operator_Crouzeix_NormalProductSymmetrized
import Theorems.Thm_norm_aeval_mul_crouzeixPolynomialAuxiliaryOperator_ball_center_le_of_isStarNormal_aeval_of_forall_symmetrized_bound

set_option autoImplicit false
open Complex Polynomial Set
open scoped InnerProductSpace Pointwise
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
theorem _root_.solution
    (A : E →L[ℂ] E) [IsStarNormal A] (c : ℂ) {R : ℝ}
    (hA : ‖A - c • (1 : E →L[ℂ] E)‖ < R)
    (hsymm : ∀ q : Polynomial ℂ,
      ‖Polynomial.aeval A q +
          star (crouzeixPolynomialAuxiliaryOperator A
            (SmoothJordanDomain.ball c R
              ((norm_nonneg (A - c • 1)).trans_lt hA)) q)‖ ≤
        2 * polynomialSupNorm q (closure (numericalRange A)))
    (p : Polynomial ℂ) :
    ‖Polynomial.aeval A p *
        crouzeixPolynomialAuxiliaryOperator A
          (SmoothJordanDomain.ball c R
            ((norm_nonneg (A - c • 1)).trans_lt hA)) p‖ ≤
      polynomialSupNorm p (closure (numericalRange A)) ^ 2 := by
  have hnormal : IsStarNormal (Polynomial.aeval A p) := by
    rw [← cfc_polynomial p A]
    exact cfc_predicate _ A
  let _ := hnormal
  exact
    norm_aeval_mul_crouzeixPolynomialAuxiliaryOperator_ball_center_le_of_isStarNormal_aeval_of_forall_symmetrized_bound
      A c hA hsymm p
