-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_LBr2_chi_eight_lift_values
-- name    : Formalism.LFunctionChainParameters.LBr2.chi_eight_lift_values
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T01:39:41.127002+00:00
-- url     : https://prove2.me/theorems/4fe879cc-c675-4f27-9504-2a6d5ad7d79f
-- title:
--   LBr2: chi eight lift values
-- statement:
--   The LBr2 construction uses the chi eight lift values property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/PrimeCongruenceConditions.lean#L398-L424
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/PrimeCongruenceConditions.lean#L398-L424

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

theorem Formalism.LFunctionChainParameters.LBr2.chi_eight_lift_values (e : ℕ) (h8 : 8 ∣ 2 ^ (e + 2)) :
    changeLevel h8 chi8 ((-1 : (ZMod (2 ^ (e + 2)))ˣ) : ZMod (2 ^ (e + 2))) = 1 ∧
    changeLevel h8 chi8 ((TwoAdicCyclotomicDecomposition.u5 (e + 2) : (ZMod (2 ^ (e + 2)))ˣ) : ZMod (2 ^ (e + 2))) = -1 := by sorry
