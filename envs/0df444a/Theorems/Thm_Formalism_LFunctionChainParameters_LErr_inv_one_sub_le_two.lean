-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_LErr_inv_one_sub_le_two
-- name    : Formalism.LFunctionChainParameters.LErr.inv_one_sub_le_two
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:30:28.124217+00:00
-- url     : https://prove2.me/theorems/7027b5c4-c9c9-460e-a0a9-d49c8d2cd7cb
-- title:
--   LErr: inv one sub le two
-- statement:
--   The LErr construction uses the inv one sub le two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/SubThreeMulLogTwoLe.lean#L252-L256
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/SubThreeMulLogTwoLe.lean#L252-L256

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

theorem Formalism.LFunctionChainParameters.LErr.inv_one_sub_le_two {d : ℝ} (hd : d ≤ 1 / 2) : 0 ≤ (1 - d)⁻¹ ∧ (1 - d)⁻¹ ≤ 2 := by sorry
