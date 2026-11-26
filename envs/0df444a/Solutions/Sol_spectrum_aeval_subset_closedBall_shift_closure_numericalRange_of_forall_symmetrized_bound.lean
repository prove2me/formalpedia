-- Prove2me | solution 1 for spectrum_aeval_subset_closedBall_shift_closure_numericalRange_of_forall_symmetrized_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:59:00.370892+00:00
-- url     : https://prove2.me/submissions/40a09174-c38f-42e9-b075-858f730950c0

import Definitions.Def_Operator_Crouzeix_ConvexRunge
import Definitions.Def_Operator_Crouzeix_NormalProduct
import Definitions.Def_Operator_Crouzeix_SmoothSupportDomain
import Definitions.Def_Operator_NumericalRange_Convex
import Definitions.Def_Operator_NumericalRange_Nonempty
import Definitions.Def_Operator_Crouzeix_NormalProductSymmetrized
import Theorems.Thm_spectrum_aeval_subset_closedBall_shift_of_isCompact_nonempty_convex_of_forall_symmetrized_bound
import Theorems.Thm_closure_numericalRange_nonempty_iff_nontrivial
import Theorems.Thm_convex_numericalRange
import Theorems.Thm_isBounded_numericalRange


set_option autoImplicit false
open Complex Polynomial Set
open scoped InnerProductSpace Pointwise
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
theorem _root_.solution
    (A : E →L[ℂ] E) (c : ℂ) {R : ℝ}
    (hA : ‖A - c • (1 : E →L[ℂ] E)‖ < R)
    (hsymm : ∀ q : Polynomial ℂ,
      ‖Polynomial.aeval A q +
          star (crouzeixPolynomialAuxiliaryOperator A
            (SmoothJordanDomain.ball c R
              ((norm_nonneg (A - c • 1)).trans_lt hA)) q)‖ ≤
        2 * polynomialSupNorm q (closure (numericalRange A)))
    (p : Polynomial ℂ) (b : ℂ) :
    spectrum ℂ (Polynomial.aeval A p) ⊆
      Metric.closedBall b
        (polynomialSupNorm (p - Polynomial.C b)
          (closure (numericalRange A))) := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · let _ := hE
    rw [spectrum.of_subsingleton]
    exact Set.empty_subset _
  let _ := hE
  exact
    spectrum_aeval_subset_closedBall_shift_of_isCompact_nonempty_convex_of_forall_symmetrized_bound
      A (isBounded_numericalRange A).isCompact_closure
        ((closure_numericalRange_nonempty_iff_nontrivial A).2 inferInstance)
        (convex_numericalRange A).closure c hA hsymm p b
