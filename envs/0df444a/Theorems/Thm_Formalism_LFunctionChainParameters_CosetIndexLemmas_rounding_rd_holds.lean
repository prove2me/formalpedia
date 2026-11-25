-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_CosetIndexLemmas_rounding_rd_holds
-- name    : Formalism.LFunctionChainParameters.CosetIndexLemmas.rounding_rd_holds
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T01:38:54.803607+00:00
-- url     : https://prove2.me/theorems/ee3c1b8c-8ded-474f-8fde-d1ed04a2c888
-- title:
--   Coset Index Lemmas: rounding rd holds
-- statement:
--   The Coset Index Lemmas construction uses the rounding rd holds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/DisplayedInequalitySharpHalf.lean#L22-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/DisplayedInequalitySharpHalf.lean#L22-L88

import Definitions.Def_Formalism_SizeWindowBrackets_GrowthBracketBoundOfSizeWindows
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_GaloisMapComplexConjugation
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_LipschitzWeightAndMinimum
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_AdmissibleSchurLemma
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_CorollaryModelSideCondition
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_WeightedMeanLemmaNeedsDegree
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_DisplayedInequalitySharpHalf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.CosetIndexLemmas
open Formalism Formalism.D5 Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LHost
open Formalism.LFunctionChainParameters.DeficitSplitLemmas

theorem Formalism.LFunctionChainParameters.CosetIndexLemmas.rounding_rd_holds : RoundingRd := by sorry
