-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_SmallOrderPrimeLosses_second_discriminant_bound
-- name    : Formalism.LFunctionChainParameters.SmallOrderPrimeLosses.second_discriminant_bound
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T09:50:05.801653+00:00
-- url     : https://prove2.me/theorems/a8e4de9c-b15c-4588-b808-e036c4596265
-- title:
--   Small Order Prime Losses: second discriminant bound
-- statement:
--   The Small Order Prime Losses construction uses the second discriminant bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/DiscriminantSettingSatisfied.lean#L76-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/DiscriminantSettingSatisfied.lean#L76-L94

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

theorem Formalism.LFunctionChainParameters.SmallOrderPrimeLosses.second_discriminant_bound : SecondD := by sorry
