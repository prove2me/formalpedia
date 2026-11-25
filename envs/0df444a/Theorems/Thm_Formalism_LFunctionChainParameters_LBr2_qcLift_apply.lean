-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_LBr2_qcLift_apply
-- name    : Formalism.LFunctionChainParameters.LBr2.qcLift_apply
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T02:01:22.145005+00:00
-- url     : https://prove2.me/theorems/09976870-8813-5e68-8540-b134281651cf
-- title:
--   LBr2: qc Lift apply
-- statement:
--   The LBr2 construction uses the qc Lift apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/PrimeCongruenceConditions.lean#L192-L198
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/PrimeCongruenceConditions.lean#L192-L198

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

theorem Formalism.LFunctionChainParameters.LBr2.qcLift_apply {N l : ℕ} [Fact l.Prime] (h : l ∣ N) (u : (ZMod N)ˣ) :
    changeLevel h (qc l) (u : ZMod N)
      = ((((quadraticChar (ZMod l)).toUnitHom (ZMod.unitsMap h u) : ℤˣ) : ℤ) : ℂ) := by sorry
