-- Prove2me | Theorems.Thm_ClassicalComplexWPT_exists_scale_normalized_close_half
-- name    : ClassicalComplexWPT.exists_scale_normalized_close_half
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:03:14.68753+00:00
-- url     : https://prove2.me/theorems/1bd0cfa2-f901-4c0d-9de2-de2c50ba2ac2
-- title:
--   Classical Complex WPT: exists scale normalized close half
-- statement:
--   The Classical Complex WPT construction uses the exists scale normalized close half property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/NormalizedCoefficients.lean#L119-L147
-- source:
--   https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/NormalizedCoefficients.lean#L119-L147

import Definitions.Def_ClassicalComplexWPT_AnalyticSeries
import Definitions.Def_ClassicalComplexWPT_ExactOrder
import Definitions.Def_ClassicalComplexWPT_WeightedSeries
import Definitions.Def_ClassicalComplexWPT_WeightedCoefficientMap
import Definitions.Def_ClassicalComplexWPT_NormalizedCoefficients
set_option autoImplicit true
open Filter
open scoped BigOperators ENNReal NNReal Topology
noncomputable section
set_option maxHeartbeats 1000000
open ClassicalComplexWPT

theorem ClassicalComplexWPT.exists_scale_normalized_close_half (f : OriginSeq) (d : ℕ)
    (hlow : ∀ j < d, f j = 0) (hfd : f d ≠ 0) :
    ∃ (t : ℝ≥0) (ht : t ≤ 1), 0 < t ∧ t < 1 ∧
      ‖normalizedScale t ht f d - monomialSeq d‖ < (1 : ℝ) / 2 := by sorry
