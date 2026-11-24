-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_SmallOrderPrimeLosses_sizeOut_core
-- name    : Formalism.LFunctionChainParameters.SmallOrderPrimeLosses.sizeOut_core
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T09:50:21.089495+00:00
-- url     : https://prove2.me/theorems/0cc18b2d-4174-4b44-9629-202430d260d5
-- title:
--   Small Order Prime Losses: size Out core
-- statement:
--   The Small Order Prime Losses construction uses the size Out core property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/DiscriminantSettingSatisfied.lean#L114-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/DiscriminantSettingSatisfied.lean#L114-L129

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

theorem Formalism.LFunctionChainParameters.SmallOrderPrimeLosses.sizeOut_core {P : Par} {e K m T : ℝ} (hW : Windows P e K) (hL : LargeX P.x P.ε e K) (hm : 0 ≤ m)
    (hT : 1 ≤ T) : tOutD P m T ≤ sg P K * unitU P m T := by sorry
