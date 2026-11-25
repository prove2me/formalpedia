-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_LBr2_comp_neg
-- name    : Formalism.LFunctionChainParameters.LBr2.comp_neg
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T01:35:22.152636+00:00
-- url     : https://prove2.me/theorems/e4bc53e3-95dd-45c2-8cb9-fca3aedb5a19
-- title:
--   LBr2: comp neg
-- statement:
--   The LBr2 construction uses the comp neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/PrimeCongruenceConditions.lean#L222-L229
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/PrimeCongruenceConditions.lean#L222-L229

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

theorem Formalism.LFunctionChainParameters.LBr2.comp_neg (ψ : AddChar (E0 × HA e) ℂ) (f : ZMod 2 → E0 × HA e) (f0 : f 0 = 0) (h1 : ψ (f 1) = -1) (s : ℤˣ) :
    ψ (f (Multiplicative.toAdd (LHost.sgn2 s))) = ((s : ℤ) : ℂ) := by sorry
