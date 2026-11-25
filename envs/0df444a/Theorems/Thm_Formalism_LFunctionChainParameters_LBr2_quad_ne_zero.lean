-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_LBr2_quad_ne_zero
-- name    : Formalism.LFunctionChainParameters.LBr2.quad_ne_zero
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T01:42:19.459281+00:00
-- url     : https://prove2.me/theorems/5f0c6016-5252-490a-a16e-ec3dca5b1d81
-- title:
--   LBr2: quad ne zero
-- statement:
--   The LBr2 construction uses the quad ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/PrimeCongruenceConditions.lean#L306-L317
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/PrimeCongruenceConditions.lean#L306-L317

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

theorem Formalism.LFunctionChainParameters.LBr2.quad_ne_zero (e : ℕ) : (psC : AddChar (E0 × HA e) ℂ) ≠ 0 ∧ (chC : AddChar (E0 × HA e) ℂ) ≠ 0 ∧
    (chpsC : AddChar (E0 × HA e) ℂ) ≠ 0 := by sorry
