-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_LBr2_real_cases
-- name    : Formalism.LFunctionChainParameters.LBr2.real_cases
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T01:53:20.219999+00:00
-- url     : https://prove2.me/theorems/7e27f7b3-a8d0-4c88-ac16-b81c20fcd0d8
-- title:
--   LBr2: real cases
-- statement:
--   The LBr2 construction uses the real cases property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/PrimeCongruenceConditions.lean#L458-L493
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/PrimeCongruenceConditions.lean#L458-L493

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

theorem Formalism.LFunctionChainParameters.LBr2.real_cases (h : FrobeniusOrbits.HostHyp q d) (ψ : AddChar (E0 × HA e) ℂ) {t : ℕ} (θ : DirichletCharacter ℂ t)
    (ht : t ∣ 2 ^ (e + 2)) (hθ : θ.IsPrimitive)
    (h2 : ∀ u : (ZMod (hostN e q d))ˣ, changeLevel (ht.trans (two_dvd_hostN e q d)) θ (u : ZMod _)
      = ψ ((0, 0), Additive.ofMul (FrobeniusOrbits.hcl e (ZMod.unitsMap (two_dvd_hostN e q d) u)))) :
    dirChar (recMap e q d) ψ = changeLevel (ht.trans (two_dvd_hostN e q d)) θ ∨
    SameChar (chiOf e q d ψ) (tw θ q) ∨ SameChar (chiOf e q d ψ) (tw θ d) ∨
    SameChar (chiOf e q d ψ) (tw (tw θ q) d) := by sorry
