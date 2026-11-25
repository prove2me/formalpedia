-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_LBr2_thin_caseA
-- name    : Formalism.LFunctionChainParameters.LBr2.thin_caseA
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T01:41:33.611348+00:00
-- url     : https://prove2.me/theorems/f5e459cf-f1a3-50fd-8e21-fd3558ed906e
-- title:
--   LBr2: thin case A
-- statement:
--   The LBr2 construction uses the thin case A property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/PrimeCongruenceConditions.lean#L620-L646
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/PrimeCongruenceConditions.lean#L620-L646

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

theorem Formalism.LFunctionChainParameters.LBr2.thin_caseA (a A μ s R : ℝ) (ha : 0 < a) (hA : 0 ≤ A) (hμ2 : 2 ≤ μ) (hμs : μ ≤ s) (hsR : R / 2 ≤ s) :
    A * (μ + s + s ^ 2) ^ 3 * Real.exp (-a * s ^ 2 / (μ + s))
      ≤ 8 * A * (((6 : ℕ).factorial : ℝ) / (a / 4) ^ 6) * Real.exp (-(a / 8 * R)) := by sorry
