-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_PhiMonotonicityLemmas_corollary_model_side_condition
-- name    : Formalism.LFunctionChainParameters.PhiMonotonicityLemmas.corollary_model_side_condition
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T09:02:51.350808+00:00
-- url     : https://prove2.me/theorems/d11aa3f3-9208-40f3-b185-d3bf1154a5fa
-- title:
--   Phi Monotonicity Lemmas: corollary model side condition
-- statement:
--   The Phi Monotonicity Lemmas construction uses the corollary model side condition property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/CorollaryModelSideCondition.lean#L9-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/CorollaryModelSideCondition.lean#L9-L21

import Definitions.Def_Formalism_SizeWindowBrackets_SlopeExcessBoundExponentZero
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_WeightedMeanLemmaNeedsDegree
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_WeightedMeanData
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_CorollaryModelSideCondition
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Real Filter
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.PhiMonotonicityLemmas

theorem Formalism.LFunctionChainParameters.PhiMonotonicityLemmas.corollary_model_side_condition :
    (0 + 1 + ErrF (1 / 8) 1 32 (5 * (1 / 32) + 3 * (1 / 192)) (2 * (1 / 131072))) - 0 ≤ (32 : ℝ) := by sorry
