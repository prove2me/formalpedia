-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_LBr2_compQ_neg
-- name    : Formalism.LFunctionChainParameters.LBr2.compQ_neg
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T01:45:55.288052+00:00
-- url     : https://prove2.me/theorems/3404404f-f98c-447d-a08b-10496a4d81c3
-- title:
--   LBr2: comp Q neg
-- statement:
--   The LBr2 construction uses the comp Q neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/PrimeCongruenceConditions.lean#L251-L255
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/PrimeCongruenceConditions.lean#L251-L255

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

theorem Formalism.LFunctionChainParameters.LBr2.compQ_neg (ψ : AddChar (E0 × HA e) ℂ) (h1 : ψ ((0, 1), 0) = -1) (u : (ZMod (hostN e q d))ˣ) :
    changeLevel (q_dvd_hostN e q d) (qc q) (u : ZMod _)
      = ψ ((0, sQ q (ZMod.unitsMap (q_dvd_hostN e q d) u)), 0) := by sorry
