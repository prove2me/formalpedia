-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_LErr_log_one_add_rpow_le
-- name    : Formalism.LFunctionChainParameters.LErr.log_one_add_rpow_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:30:38.455804+00:00
-- url     : https://prove2.me/theorems/d0be87c0-2749-47d7-a515-06623d9ba8ca
-- title:
--   LErr: log one add rpow le
-- statement:
--   The LErr construction uses the log one add rpow le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/SubThreeMulLogTwoLe.lean#L220-L234
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/SubThreeMulLogTwoLe.lean#L220-L234

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

theorem Formalism.LFunctionChainParameters.LErr.log_one_add_rpow_le {x c y : ℝ} (hx : 1 ≤ x) (hc : 0 ≤ c) (hlog : Real.log x ≤ y)
    (hy : 1 ≤ y) : Real.log (1 + x ^ c) ≤ (1 + c) * y := by sorry
