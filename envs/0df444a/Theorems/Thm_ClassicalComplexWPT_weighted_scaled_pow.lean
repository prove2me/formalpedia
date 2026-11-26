-- Prove2me | Theorems.Thm_ClassicalComplexWPT_weighted_scaled_pow
-- name    : ClassicalComplexWPT.weighted_scaled_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:10:58.626134+00:00
-- url     : https://prove2.me/theorems/50826c8d-f5b1-4586-ac80-9ec44ff6e859
-- title:
--   Classical Complex WPT: weighted scaled pow
-- statement:
--   The Classical Complex WPT construction uses the weighted scaled pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/PublicExistence.lean#L36-L40
-- source:
--   https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/PublicExistence.lean#L36-L40

import Definitions.Def_ClassicalComplexWPT_PreparationSequences
import Definitions.Def_ClassicalComplexWPT_WeightedEvaluation
import Definitions.Def_ClassicalComplexWPT_L1PolynomialEvaluation
import Definitions.Def_ClassicalComplexWPT_WeightedGermEvaluation
import Definitions.Def_ClassicalComplexWPT_PublicExistence
set_option autoImplicit true
open Filter
open scoped BigOperators ENNReal NNReal Topology
noncomputable section
set_option maxHeartbeats 1000000
open ClassicalComplexWPT

theorem ClassicalComplexWPT.weighted_scaled_pow (r : ℂ) (hr : r ≠ 0) {d i : ℕ} (hi : i ≤ d)
    (w : ℂ) :
    r ^ (d - i) * w ^ i = r ^ d * (r⁻¹ * w) ^ i := by sorry
