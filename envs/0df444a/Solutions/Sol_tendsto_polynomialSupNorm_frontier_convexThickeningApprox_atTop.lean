-- Prove2me | solution 1 for tendsto_polynomialSupNorm_frontier_convexThickeningApprox_atTop
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:22:01.881628+00:00
-- url     : https://prove2.me/submissions/3695deea-bc91-4a77-89f9-5acc7e755683

import Definitions.Def_Operator_Crouzeix_ApproximationSupNorm
import Definitions.Def_Operator_Crouzeix_BoundaryMaximum
import Definitions.Def_Operator_Crouzeix_CompactThickeningApprox
import Definitions.Def_Operator_Crouzeix_BoundaryApproximation
import Theorems.Thm_polynomialSupNorm_frontier_convexThickeningApprox_eq_compactThickeningApprox
import Theorems.Thm_compactThickeningApprox_spec
import Theorems.Thm_mem_numericalRange
import Theorems.Thm_tendsto_polynomialSupNorm_atTop_of_antitone_isCompact
attribute [local simp] mem_numericalRange



set_option autoImplicit false
open Filter Polynomial Set
theorem _root_.solution
    (p : Polynomial ℂ) {K : Set ℂ} (hK : IsCompact K) :
    Tendsto
      (fun n ↦ polynomialSupNorm p (frontier (convexThickeningApprox K n))) atTop
      (nhds (polynomialSupNorm p K)) := by
  rcases K.eq_empty_or_nonempty with hKempty | hKne
  · subst K
    simpa only [convexThickeningApprox, Metric.thickening_empty, frontier_empty,
      polynomialSupNorm, Set.mem_empty_iff_false, Real.iSup_of_isEmpty,
      Real.iSup_const_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (0 : ℝ)) atTop (nhds 0))
  · obtain ⟨hanti, hcompact, hnonempty, hinter⟩ :=
      compactThickeningApprox_spec K hK hKne
    have ht := tendsto_polynomialSupNorm_atTop_of_antitone_isCompact p
      (compactThickeningApprox K) hanti hcompact hnonempty
    rw [hinter] at ht
    simpa only [
      polynomialSupNorm_frontier_convexThickeningApprox_eq_compactThickeningApprox
        p hK.isBounded] using ht
