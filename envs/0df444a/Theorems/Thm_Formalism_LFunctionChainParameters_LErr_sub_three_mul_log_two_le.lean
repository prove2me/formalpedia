-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_LErr_sub_three_mul_log_two_le
-- name    : Formalism.LFunctionChainParameters.LErr.sub_three_mul_log_two_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:30:35.155452+00:00
-- url     : https://prove2.me/theorems/292ad4e6-c16b-4b5f-a0cc-88abf54a56e1
-- title:
--   LErr: sub three mul log two le
-- statement:
--   The LErr construction uses the sub three mul log two le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/SubThreeMulLogTwoLe.lean#L244-L250
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/SubThreeMulLogTwoLe.lean#L244-L250

import Definitions.Def_Formalism_SizeWindowBrackets_ErrorFormsWeakWindowsFalse
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_SubThreeMulLogTwoLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Real
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.LErr
open Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds
set_option linter.unusedVariables false

theorem Formalism.LFunctionChainParameters.LErr.sub_three_mul_log_two_le {k : ℝ} (hk : 0 ≤ k) : (k - 3) * Real.log 2 ≤ k := by sorry
