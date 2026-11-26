-- Prove2me | Theorems.Thm_ClassicalComplexWPT_normalizedScale_sub_monomial_apply_lt
-- name    : ClassicalComplexWPT.normalizedScale_sub_monomial_apply_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:02:55.870801+00:00
-- url     : https://prove2.me/theorems/291fde83-54a4-5504-a8cf-543b95131208
-- title:
--   Classical Complex WPT: normalized Scale sub monomial apply lt
-- statement:
--   The Classical Complex WPT construction uses the normalized Scale sub monomial apply lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/NormalizedCoefficients.lean#L61-L100
-- source:
--   https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/NormalizedCoefficients.lean#L61-L100

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

theorem ClassicalComplexWPT.normalizedScale_sub_monomial_apply_lt {t : ℝ≥0} (ht : t ≤ 1) (ht0 : 0 < t)
    (f : OriginSeq) (d k : ℕ) (hlow : ∀ j < d, f j = 0) (hfd : f d ≠ 0) :
    ‖(normalizedScale t ht f d - monomialSeq d) k‖ ≤
      ((t : ℝ) / ‖f d‖) * ‖f k‖ := by sorry
