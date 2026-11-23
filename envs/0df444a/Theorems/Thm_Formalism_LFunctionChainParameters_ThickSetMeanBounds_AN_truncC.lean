-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_ThickSetMeanBounds_AN_truncC
-- name    : Formalism.LFunctionChainParameters.ThickSetMeanBounds.AN.truncC
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:36:53.679308+00:00
-- url     : https://prove2.me/theorems/dc7f9749-a4f2-47d3-8a46-69ecd43cc4b6
-- title:
--   AN: trunc C
-- statement:
--   The AN construction uses the trunc C property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/LipschitzWeightAndMinimum.lean#L695-L717
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/LipschitzWeightAndMinimum.lean#L695-L717

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
open Formalism.LFunctionChainParameters.ThickSetMeanBounds.AN

theorem Formalism.LFunctionChainParameters.ThickSetMeanBounds.AN.truncC (c : ℕ → ℂ) (y : ℝ) (M : ℕ) (hM : ⌊y⌋₊ ≤ M) :
    ∑ n ∈ Icc 1 ⌊y⌋₊, c n * ((y / n - 1 : ℝ) : ℂ) = ∑ n ∈ Icc 1 M, c n * ((max (y / n - 1) 0 : ℝ) : ℂ) := by sorry
