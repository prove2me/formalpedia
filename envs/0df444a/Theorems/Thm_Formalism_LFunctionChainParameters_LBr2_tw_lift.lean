-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_LBr2_tw_lift
-- name    : Formalism.LFunctionChainParameters.LBr2.tw_lift
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T01:45:44.208727+00:00
-- url     : https://prove2.me/theorems/ea17fc23-b042-41db-9331-61a2cc589acc
-- title:
--   LBr2: tw lift
-- statement:
--   The LBr2 construction uses the tw lift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/PrimeCongruenceConditions.lean#L200-L204
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/PrimeCongruenceConditions.lean#L200-L204

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

theorem Formalism.LFunctionChainParameters.LBr2.tw_lift {N t l : ℕ} [Fact l.Prime] (θ : DirichletCharacter ℂ t) (h : t * l ∣ N) :
    changeLevel h (tw θ l) = changeLevel ((Dvd.intro l rfl).trans h) θ
      * changeLevel ((Dvd.intro_left t rfl).trans h) (qc l) := by sorry
