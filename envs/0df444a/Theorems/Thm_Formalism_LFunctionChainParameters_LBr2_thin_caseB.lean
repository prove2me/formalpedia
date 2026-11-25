-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_LBr2_thin_caseB
-- name    : Formalism.LFunctionChainParameters.LBr2.thin_caseB
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T01:55:43.333476+00:00
-- url     : https://prove2.me/theorems/11d66423-bb57-4361-b978-d73097f7d387
-- title:
--   LBr2: thin case B
-- statement:
--   The LBr2 construction uses the thin case B property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/PrimeCongruenceConditions.lean#L648-L680
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/PrimeCongruenceConditions.lean#L648-L680

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

theorem Formalism.LFunctionChainParameters.LBr2.thin_caseB (a A μ s R Lb : ℝ) (ha : 0 < a) (hA : 0 ≤ A) (hμ2 : 2 ≤ μ) (hs0 : 0 ≤ s) (hsμ : s < μ)
    (hμL : μ ≤ Lb) (hv : Lb * R / 2 ≤ s ^ 2) (hL6 : Lb ^ 6 = R ^ 10) (hR0 : 0 ≤ R) :
    A * (μ + s + s ^ 2) ^ 3 * Real.exp (-a * s ^ 2 / (μ + s))
      ≤ 8 * A * (((10 : ℕ).factorial : ℝ) / (a / 8) ^ 10) * Real.exp (-(a / 8 * R)) := by sorry
