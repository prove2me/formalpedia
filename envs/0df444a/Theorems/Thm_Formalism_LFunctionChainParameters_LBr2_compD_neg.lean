-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_LBr2_compD_neg
-- name    : Formalism.LFunctionChainParameters.LBr2.compD_neg
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T01:48:04.942929+00:00
-- url     : https://prove2.me/theorems/ff347bb4-c91a-4a2c-bdc5-5d8da0946179
-- title:
--   LBr2: comp D neg
-- statement:
--   The LBr2 construction uses the comp D neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/PrimeCongruenceConditions.lean#L257-L261
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/PrimeCongruenceConditions.lean#L257-L261

import Definitions.Def_Formalism_SizeWindowBrackets_SmoothedRemainderRealIntegralFormula
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_GaloisMapComplexConjugation
import Definitions.Def_Formalism_LandauZeroFreeBounds_SiegelWalfiszAPOfSiegelLower
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_PrimeCongruenceConditions
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Filter Topology ArithmeticFunction DirichletCharacter
noncomputable section
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.LBr2
open Formalism Formalism.D5 Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LHost Formalism.LFunctionChainParameters.LErr Formalism.LFunctionChainParameters.LChain
  Formalism.LFunctionChainParameters.LChain2
variable {e q d : ℕ} [Fact q.Prime] [Fact d.Prime]

theorem Formalism.LFunctionChainParameters.LBr2.compD_neg (ψ : AddChar (E0 × HA e) ℂ) (h1 : ψ ((1, 0), 0) = -1) (u : (ZMod (hostN e q d))ˣ) :
    changeLevel (d_dvd_hostN e q d) (qc d) (u : ZMod _)
      = ψ ((sQ d (ZMod.unitsMap (d_dvd_hostN e q d) u), 0), 0) := by sorry
