-- Prove2me | solution 1 for polynomialSupNorm_closure_eq_frontier_of_isBounded
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:56:37.332842+00:00
-- url     : https://prove2.me/submissions/35248186-1afc-4664-8609-919c77b66d02

import Mathlib.Analysis.Complex.AbsMax
import Definitions.Def_Operator_Crouzeix_ApproximationSupNorm
import Definitions.Def_Operator_Crouzeix_GeneralSymmetrized
import Definitions.Def_Operator_Crouzeix_BoundaryMaximum
import Theorems.Thm_bddAbove_norm_eval_image_of_isCompact
import Theorems.Thm_norm_eval_le_polynomialSupNorm

section
open Complex Polynomial Set
private theorem polynomialSupNorm_eq_of_isMaxOn_boundaryMaximum
    (p : Polynomial ℂ) {K : Set ℂ} (hK : IsCompact K) {z : ℂ}
    (hz : z ∈ K) (hmax : IsMaxOn (fun w => ‖p.eval w‖) K z) :
    polynomialSupNorm p K = ‖p.eval z‖ := by
  apply le_antisymm
  · unfold polynomialSupNorm
    refine Real.iSup_le (fun w => ?_) (norm_nonneg _)
    exact Real.iSup_le (fun hw => hmax hw) (norm_nonneg _)
  · exact norm_eval_le_polynomialSupNorm p
      (bddAbove_norm_eval_image_of_isCompact p hK) hz
end

set_option autoImplicit false
open Complex Polynomial Set
theorem _root_.solution
    (p : Polynomial ℂ) {U : Set ℂ} (hU : Bornology.IsBounded U) :
    polynomialSupNorm p (closure U) = polynomialSupNorm p (frontier U) := by
  rcases U.eq_empty_or_nonempty with rfl | hUne
  · rw [closure_empty, frontier_empty]
  have hclosure : IsCompact (closure U) := hU.isCompact_closure
  have hfrontier : IsCompact (frontier U) :=
    hclosure.of_isClosed_subset isClosed_frontier frontier_subset_closure
  obtain ⟨z, hz, hmax⟩ :=
    Complex.exists_mem_frontier_isMaxOn_norm hU hUne p.differentiable.diffContOnCl
  rw [polynomialSupNorm_eq_of_isMaxOn_boundaryMaximum p hclosure
      (frontier_subset_closure hz) hmax,
    polynomialSupNorm_eq_of_isMaxOn_boundaryMaximum p hfrontier hz
      (hmax.on_subset frontier_subset_closure)]
