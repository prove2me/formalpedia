-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_SmallOrderPrimeLosses_logdiv_nonneg
-- name    : Formalism.LFunctionChainParameters.SmallOrderPrimeLosses.logdiv_nonneg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:57:05.677801+00:00
-- url     : https://prove2.me/theorems/2a2515bb-b3e4-4349-99c2-373ead859c83
-- title:
--   Small Order Prime Losses: logdiv nonneg
-- statement:
--   The Small Order Prime Losses construction uses the logdiv nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/DiscriminantSettingSatisfied.lean#L29-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/DiscriminantSettingSatisfied.lean#L29-L30

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

theorem Formalism.LFunctionChainParameters.SmallOrderPrimeLosses.logdiv_nonneg (p : ℕ) : 0 ≤ Real.log (p : ℝ) / (p : ℝ) := by sorry
