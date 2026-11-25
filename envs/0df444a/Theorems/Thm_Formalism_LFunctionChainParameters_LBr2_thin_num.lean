-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_LBr2_thin_num
-- name    : Formalism.LFunctionChainParameters.LBr2.thin_num
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T01:48:24.906745+00:00
-- url     : https://prove2.me/theorems/3ac75f11-acfd-5c11-9f40-00a5a3b51646
-- title:
--   LBr2: thin num
-- statement:
--   The LBr2 construction uses the thin num property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/PrimeCongruenceConditions.lean#L682-L760
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/PrimeCongruenceConditions.lean#L682-L760

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

theorem Formalism.LFunctionChainParameters.LBr2.thin_num (ε a A : ℝ) (hε : 0 < ε) (ha : 0 < a) (hA : 0 ≤ A) :
    ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∀ μ v : ℝ, 2 ≤ μ → μ ≤ 2 * x ^ (ε / 5) * Real.log x ^ 2 + 2 → x ^ (ε / 3) / 2 ≤ v →
      A * (μ + Real.sqrt v + v) ^ 3 * Real.exp (-a * v / (μ + Real.sqrt v)) ≤ Real.exp (-(a / 16) * x ^ (ε / 8)) := by sorry
