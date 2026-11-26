-- Prove2me | solution 1 for norm_eval_boundaryParam_le_polynomialSupNorm_frontier
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:54:40.514397+00:00
-- url     : https://prove2.me/submissions/a08e0f15-8c0d-47ba-89f2-5ec0656e2434

import Definitions.Def_Operator_Crouzeix_ApproximationSupNorm
import Definitions.Def_Operator_Crouzeix_DoubleLayer
import Definitions.Def_Operator_Crouzeix_DoubleLayerIntegral
import Definitions.Def_Operator_Crouzeix_PositiveIntegral
import Definitions.Def_Operator_Crouzeix_ProductContour
import Definitions.Def_Operator_Crouzeix_SymmetrizedAuxiliary
import Definitions.Def_Operator_Crouzeix_SymmetrizedBound
import Definitions.Def_Operator_Crouzeix_GeneralSymmetrized
import Theorems.Thm_SmoothJordanDomain_isCompact_frontier
import Theorems.Thm_bddAbove_norm_eval_image_of_isCompact
import Theorems.Thm_norm_eval_le_polynomialSupNorm


set_option autoImplicit false
open Complex MeasureTheory Set
open scoped InnerProductSpace Interval Real
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
theorem _root_.solution
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ) (t : ℝ) :
    ‖Polynomial.eval (Omega.boundaryParam t) p‖ ≤
      polynomialSupNorm p (frontier Omega.carrier) := by
  apply norm_eval_le_polynomialSupNorm p
  · exact bddAbove_norm_eval_image_of_isCompact p Omega.isCompact_frontier
  · rw [← Omega.boundaryParam_range]
    exact mem_range_self t
