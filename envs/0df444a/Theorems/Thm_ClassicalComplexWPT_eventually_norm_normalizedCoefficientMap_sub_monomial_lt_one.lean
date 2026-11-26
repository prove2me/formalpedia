-- Prove2me | Theorems.Thm_ClassicalComplexWPT_eventually_norm_normalizedCoefficientMap_sub_monomial_lt_one
-- name    : ClassicalComplexWPT.eventually_norm_normalizedCoefficientMap_sub_monomial_lt_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:03:27.950795+00:00
-- url     : https://prove2.me/theorems/66a07262-d087-5701-80d0-6e33813ffb6f
-- title:
--   Classical Complex WPT: eventually norm normalized Coefficient Map sub monomial lt one
-- statement:
--   The Classical Complex WPT construction uses the eventually norm normalized Coefficient Map sub monomial lt one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/NormalizedCoefficients.lean#L266-L281
-- source:
--   https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/NormalizedCoefficients.lean#L266-L281

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

theorem ClassicalComplexWPT.eventually_norm_normalizedCoefficientMap_sub_monomial_lt_one {n d : ℕ}
    (C : Base n → OriginSeq) (denom : ℂ) (hC : AnalyticAt ℂ C 0)
    (hclose : ‖normalizedCoefficientMap C denom 0 - monomialSeq d‖ < (1 : ℝ) / 2) :
    ∀ᶠ z in 𝓝 (0 : Base n),
      ‖normalizedCoefficientMap C denom z - monomialSeq d‖ < 1 := by sorry
