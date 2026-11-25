-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_LBr2_component_two_neg
-- name    : Formalism.LFunctionChainParameters.LBr2.component_two_neg
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T01:50:20.784694+00:00
-- url     : https://prove2.me/theorems/c9c1ce74-3626-410a-b888-b02b7d53d131
-- title:
--   LBr2: component two neg
-- statement:
--   The LBr2 construction uses the component two neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/PrimeCongruenceConditions.lean#L446-L452
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/PrimeCongruenceConditions.lean#L446-L452

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

theorem Formalism.LFunctionChainParameters.LBr2.component_two_neg (ψ : AddChar (E0 × HA e) ℂ) (h8 : 8 ∣ 2 ^ (e + 2))
    (h1 : ψ ((0, 0), Additive.ofMul (FrobeniusOrbits.hcl e (TwoAdicCyclotomicDecomposition.u5 (e + 2)))) = -1) (u : (ZMod (hostN e q d))ˣ) :
    changeLevel (h8.trans (two_dvd_hostN e q d)) chi8 (u : ZMod _)
      = ψ ((0, 0), Additive.ofMul (FrobeniusOrbits.hcl e (ZMod.unitsMap (two_dvd_hostN e q d) u))) := by sorry
