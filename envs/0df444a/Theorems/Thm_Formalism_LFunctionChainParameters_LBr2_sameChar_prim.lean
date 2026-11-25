-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_LBr2_sameChar_prim
-- name    : Formalism.LFunctionChainParameters.LBr2.sameChar_prim
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T01:54:55.430241+00:00
-- url     : https://prove2.me/theorems/f0a6c27d-f4b0-4c6d-a21e-25ef1fd80e6a
-- title:
--   LBr2: same Char prim
-- statement:
--   The LBr2 construction uses the same Char prim property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/PrimeCongruenceConditions.lean#L93-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/PrimeCongruenceConditions.lean#L93-L105

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

theorem Formalism.LFunctionChainParameters.LBr2.sameChar_prim {N M : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hM : M ∣ N) (χ' : DirichletCharacter ℂ M)
    (hp : χ'.IsPrimitive) (hχ : χ = changeLevel hM χ') : SameChar χ.primitiveCharacter χ' := by sorry
