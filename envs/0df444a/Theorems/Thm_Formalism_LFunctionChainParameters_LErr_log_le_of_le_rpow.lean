-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_LErr_log_le_of_le_rpow
-- name    : Formalism.LFunctionChainParameters.LErr.log_le_of_le_rpow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:32:36.886002+00:00
-- url     : https://prove2.me/theorems/db9d2651-a687-4d09-b471-9a7084fb8a2a
-- title:
--   LErr: log le of le rpow
-- statement:
--   The LErr construction uses the log le of le rpow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/SubThreeMulLogTwoLe.lean#L236-L242
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/SubThreeMulLogTwoLe.lean#L236-L242

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

theorem Formalism.LFunctionChainParameters.LErr.log_le_of_le_rpow {x k e y : ℝ} (hx : 1 ≤ x) (he : 0 ≤ e) (hk : 0 < k) (hkx : k ≤ x ^ e)
    (hlog : Real.log x ≤ y) (hy : 1 ≤ y) : Real.log k ≤ (1 + e) * y := by sorry
