-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_SmallOrderPrimeLosses_discriminant_windows_iff
-- name    : Formalism.LFunctionChainParameters.SmallOrderPrimeLosses.discriminant_windows_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T09:10:20.223847+00:00
-- url     : https://prove2.me/theorems/5a3b8e14-84f3-4758-9a7e-3aca414fb80c
-- title:
--   Small Order Prime Losses: discriminant windows iff
-- statement:
--   The Small Order Prime Losses construction uses the discriminant windows iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/DiscriminantSettingSatisfied.lean#L9-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/DiscriminantSettingSatisfied.lean#L9-L21

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

theorem Formalism.LFunctionChainParameters.SmallOrderPrimeLosses.discriminant_windows_iff : WindowsDIff := by sorry
