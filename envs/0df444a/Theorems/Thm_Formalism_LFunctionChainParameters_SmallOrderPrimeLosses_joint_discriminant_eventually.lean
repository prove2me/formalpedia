-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_SmallOrderPrimeLosses_joint_discriminant_eventually
-- name    : Formalism.LFunctionChainParameters.SmallOrderPrimeLosses.joint_discriminant_eventually
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T09:50:12.857797+00:00
-- url     : https://prove2.me/theorems/fa108ff8-e683-4884-adbe-8b6d06f7da7a
-- title:
--   Small Order Prime Losses: joint discriminant eventually
-- statement:
--   The Small Order Prime Losses construction uses the joint discriminant eventually property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/DiscriminantSettingSatisfied.lean#L234-L241
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/DiscriminantSettingSatisfied.lean#L234-L241

import Definitions.Def_Formalism_SizeWindowBrackets_PrimeClassLossHypothesesSatisfiable
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_OneLeThresholdMulPowers
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_DiscriminantSettingSatisfied
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.SmallOrderPrimeLosses
open Finset Classical
open Formalism.LFunctionChainParameters.DeficitSplitLemmas Formalism.LFunctionChainParameters.LErr Formalism.LFunctionChainParameters.PrimeWindowSizeBounds

theorem Formalism.LFunctionChainParameters.SmallOrderPrimeLosses.joint_discriminant_eventually : LossBoundsEventually := by sorry
