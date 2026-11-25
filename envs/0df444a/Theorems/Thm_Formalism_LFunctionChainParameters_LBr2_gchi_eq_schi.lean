-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_LBr2_gchi_eq_schi
-- name    : Formalism.LFunctionChainParameters.LBr2.gchi_eq_schi
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T01:45:14.276262+00:00
-- url     : https://prove2.me/theorems/b5cda888-5f73-4f01-ac39-da1721320a22
-- title:
--   LBr2: gchi eq schi
-- statement:
--   The LBr2 construction uses the gchi eq schi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/PrimeCongruenceConditions.lean#L762-L765
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/PrimeCongruenceConditions.lean#L762-L765

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

theorem Formalism.LFunctionChainParameters.LBr2.gchi_eq_schi {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (y : ℝ) :
    Gchi χ y = Formalism.ZeroFreeDirichlet.Schi χ y - Formalism.ZeroFreeDirichlet.negLD χ 1 * y := by sorry
