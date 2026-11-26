-- Prove2me | Theorems.Thm_ClassicalComplexWPT_norm_normalizedScale_sub_monomial_le
-- name    : ClassicalComplexWPT.norm_normalizedScale_sub_monomial_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:02:55.667965+00:00
-- url     : https://prove2.me/theorems/c6879798-f96e-5b6d-b957-a52fa0a4d9d1
-- title:
--   Classical Complex WPT: norm normalized Scale sub monomial le
-- statement:
--   The Classical Complex WPT construction uses the norm normalized Scale sub monomial le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/NormalizedCoefficients.lean#L102-L117
-- source:
--   https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/NormalizedCoefficients.lean#L102-L117

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

theorem ClassicalComplexWPT.norm_normalizedScale_sub_monomial_le {t : ℝ≥0} (ht : t ≤ 1) (ht0 : 0 < t)
    (f : OriginSeq) (d : ℕ) (hlow : ∀ j < d, f j = 0) (hfd : f d ≠ 0) :
    ‖normalizedScale t ht f d - monomialSeq d‖ ≤
      ((t : ℝ) / ‖f d‖) * ‖f‖ := by sorry
