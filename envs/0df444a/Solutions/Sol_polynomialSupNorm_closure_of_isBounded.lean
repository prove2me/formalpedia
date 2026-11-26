-- Prove2me | solution 1 for polynomialSupNorm_closure_of_isBounded
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:19:25.735713+00:00
-- url     : https://prove2.me/submissions/95cb9cf2-a8ff-421d-91bb-1f1911c5dcb3

import Mathlib.Analysis.Complex.AbsMax
import Definitions.Def_Operator_Crouzeix_ApproximationSupNorm
import Definitions.Def_Operator_Crouzeix_GeneralSymmetrized
import Definitions.Def_Operator_Crouzeix_BoundaryMaximum
import Theorems.Thm_bddAbove_norm_eval_image_of_isCompact
import Theorems.Thm_norm_eval_le_polynomialSupNorm
import Theorems.Thm_polynomialSupNorm_mono_of_isCompact
import Theorems.Thm_polynomialSupNorm_nonneg


set_option autoImplicit false
open Complex Polynomial Set
theorem _root_.solution
    (p : Polynomial ℂ) {X : Set ℂ} (hX : Bornology.IsBounded X) :
    polynomialSupNorm p (closure X) = polynomialSupNorm p X := by
  have hcompact : IsCompact (closure X) := hX.isCompact_closure
  have hB : BddAbove ((fun z => ‖p.eval z‖) '' X) :=
    (bddAbove_norm_eval_image_of_isCompact p hcompact).mono
      (Set.image_mono subset_closure)
  have hsub : closure X ⊆ {z | ‖p.eval z‖ ≤ polynomialSupNorm p X} := by
    apply closure_minimal
    · intro z hz
      exact norm_eval_le_polynomialSupNorm p hB hz
    · exact isClosed_le p.continuous.norm continuous_const
  apply le_antisymm
  · rw [show polynomialSupNorm p (closure X) =
      ⨆ z ∈ closure X, ‖p.eval z‖ from rfl]
    refine Real.iSup_le (fun z => ?_) (polynomialSupNorm_nonneg p X)
    exact Real.iSup_le (fun hz => hsub hz) (polynomialSupNorm_nonneg p X)
  · exact polynomialSupNorm_mono_of_isCompact p subset_closure hcompact
