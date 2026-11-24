-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_ThickSetMeanBounds_CR_signal_term
-- name    : Formalism.LFunctionChainParameters.ThickSetMeanBounds.CR.signal_term
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:37:12.066227+00:00
-- url     : https://prove2.me/theorems/4da6706c-e93c-4933-8b19-ad327c5fb5af
-- title:
--   CR: signal term
-- statement:
--   The CR construction uses the signal term property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/LipschitzWeightAndMinimum.lean#L288-L308
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/LipschitzWeightAndMinimum.lean#L288-L308

import Definitions.Def_Formalism_SizeWindowBrackets_GrowthBoundGivesRiemannHypothesis
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_RiemannHypothesisOfPowerBound
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_StronglyIrreducible
import Definitions.Def_Formalism_ThickAverageLoss_ThickAverageProofs_Balance
import Definitions.Def_Formalism_ThickAverageLoss_ThickAverageProofs_ThickAverage
import Definitions.Def_Formalism_ZetaNonvanishing_GzLipschitz
import Mathlib.NumberTheory.Chebyshev
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_LipschitzWeightAndMinimum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset ArithmeticFunction
noncomputable section
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.ThickSetMeanBounds
open Formalism Formalism.D5 Formalism.LFunctionChainParameters.characterSumData
open Formalism.LFunctionChainParameters.ThickSetMeanBounds.CR
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]

theorem Formalism.LFunctionChainParameters.ThickSetMeanBounds.CR.signal_term (D : ArithData H) (ell : AddChar (E0 × H) ℂ → ℂ) {x ε Cd CL y : ℝ} (hx : 3 ≤ x) (hCd : 0 ≤ Cd)
    (hy : |y - x| ≤ 1) (hDer : DerivInt D ell Cd) (hVal : ValuesAtX D ell x ε CL) :
    Gz x - 3 * x ^ ((1 : ℝ) / 2 + ε) - moveCost x Cd CL
      ≤ (GPsi D ell 0 y + GPsi D ell psC y - GPsi D ell chC y - GPsi D ell chpsC y).re := by sorry
