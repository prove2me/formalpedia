-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_LChain_compl_main
-- name    : Formalism.LFunctionChainParameters.LChain.compl_main
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T09:02:47.583232+00:00
-- url     : https://prove2.me/theorems/2c08bdda-11f6-428b-8b8f-6a569652bab5
-- title:
--   LChain: compl main
-- statement:
--   The LChain construction uses the compl main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/PChain.lean#L213-L220
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/PChain.lean#L213-L220

import Definitions.Def_Formalism_SizeWindowBrackets_SChain
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_LevelOfCongruence
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_LipschitzWeightAndMinimum
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_SubThreeMulLogTwoLe
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_PChain
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
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.LChain
open Formalism Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LErr
variable {U0 : Type} [Fintype U0] {W : U0 → Type} {Top : Type} [Fintype Top] {m f : ℕ}

theorem Formalism.LFunctionChainParameters.LChain.compl_main (D0 : Data U0 W Top m f) (u0 : U0) :
    D0.Main u0 = ∑ t, ((m : ℝ) * (ph (D0.aT t) - D0.aT t * (D0.gam - D0.LpL)) - D0.aT t * sLog D0 u0) := by sorry
