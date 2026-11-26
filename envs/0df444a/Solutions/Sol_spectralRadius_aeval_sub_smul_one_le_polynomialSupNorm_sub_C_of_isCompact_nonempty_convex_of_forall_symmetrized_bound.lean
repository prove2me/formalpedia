-- Prove2me | solution 1 for spectralRadius_aeval_sub_smul_one_le_polynomialSupNorm_sub_C_of_isCompact_nonempty_convex_of_forall_symmetrized_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:01:17.916806+00:00
-- url     : https://prove2.me/submissions/9953d106-8184-4063-aa0a-74281cc17435

import Definitions.Def_Operator_Crouzeix_ConvexRunge
import Definitions.Def_Operator_Crouzeix_NormalProduct
import Definitions.Def_Operator_Crouzeix_SmoothSupportDomain
import Definitions.Def_Operator_NumericalRange_Convex
import Definitions.Def_Operator_NumericalRange_Nonempty
import Definitions.Def_Operator_Crouzeix_NormalProductSymmetrized
import Theorems.Thm_circle_center_mem_of_isCompact_nonempty_convex_of_forall_symmetrized_bound
import Theorems.Thm_spectralRadius_aeval_sub_smul_one_le_polynomialSupNorm_sub_C_of_mem_of_forall_symmetrized_bound

set_option autoImplicit false
open Complex Polynomial Set
open scoped InnerProductSpace Pointwise
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
theorem _root_.solution
    (A : E →L[ℂ] E) {K : Set ℂ}
    (hcompact : IsCompact K) (hnonempty : K.Nonempty) (hconvex : Convex ℝ K)
    (c : ℂ) {R : ℝ}
    (hA : ‖A - c • (1 : E →L[ℂ] E)‖ < R)
    (hsymm : ∀ q : Polynomial ℂ,
      ‖Polynomial.aeval A q +
          star (crouzeixPolynomialAuxiliaryOperator A
            (SmoothJordanDomain.ball c R
              ((norm_nonneg (A - c • 1)).trans_lt hA)) q)‖ ≤
        2 * polynomialSupNorm q K)
    (p : Polynomial ℂ) (b : ℂ) :
    spectralRadius ℂ
        (Polynomial.aeval A p - b • (1 : E →L[ℂ] E)) ≤
      ((polynomialSupNorm (p - Polynomial.C b) K).toNNReal : ENNReal) := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · let _ := hE
    rw [Subsingleton.elim (Polynomial.aeval A p - b • 1) 0,
      spectrum.spectralRadius_zero]
    exact bot_le
  let _ := hE
  exact
    spectralRadius_aeval_sub_smul_one_le_polynomialSupNorm_sub_C_of_mem_of_forall_symmetrized_bound
      A c hA hcompact
        (circle_center_mem_of_isCompact_nonempty_convex_of_forall_symmetrized_bound
          A hcompact hnonempty hconvex c hA hsymm)
        hsymm p b
