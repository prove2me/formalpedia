-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_LBr2_pow_mul_exp_neg_le
-- name    : Formalism.LFunctionChainParameters.LBr2.pow_mul_exp_neg_le
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T01:46:37.934493+00:00
-- url     : https://prove2.me/theorems/72ed1433-1f19-417f-a1e2-51633104ebd9
-- title:
--   LBr2: pow mul exp neg le
-- statement:
--   The LBr2 construction uses the pow mul exp neg le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/PrimeCongruenceConditions.lean#L611-L618
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/PrimeCongruenceConditions.lean#L611-L618

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

theorem Formalism.LFunctionChainParameters.LBr2.pow_mul_exp_neg_le (n : ℕ) (b t : ℝ) (hb : 0 < b) (ht : 0 ≤ t) :
    t ^ n * Real.exp (-(b * t)) ≤ (n.factorial : ℝ) / b ^ n := by sorry
