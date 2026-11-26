-- Prove2me | solution 1 for polynomialSupNorm_mono_of_isCompact
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:36:54.798306+00:00
-- url     : https://prove2.me/submissions/416ecd78-5428-4005-9b43-6e98b40aa667

import Definitions.Def_Operator_Crouzeix_SmoothApprox
import Definitions.Def_Operator_Crouzeix_VonNeumann
import Definitions.Def_Operator_Crouzeix_ApproximationSupNorm
import Theorems.Thm_bddAbove_norm_eval_image_of_isCompact
import Theorems.Thm_norm_eval_le_polynomialSupNorm
import Theorems.Thm_polynomialSupNorm_nonneg


set_option autoImplicit false
open Filter Polynomial Set
theorem _root_.solution
    (p : Polynomial ℂ) {K L : Set ℂ} (hKL : K ⊆ L) (hL : IsCompact L) :
    polynomialSupNorm p K ≤ polynomialSupNorm p L := by
  rw [show polynomialSupNorm p K =
    ⨆ z ∈ K, ‖Polynomial.eval z p‖ from rfl]
  refine Real.iSup_le (fun z ↦ ?_) (polynomialSupNorm_nonneg p L)
  exact Real.iSup_le (fun hz ↦
    norm_eval_le_polynomialSupNorm p
      (bddAbove_norm_eval_image_of_isCompact p hL) (hKL hz))
    (polynomialSupNorm_nonneg p L)
