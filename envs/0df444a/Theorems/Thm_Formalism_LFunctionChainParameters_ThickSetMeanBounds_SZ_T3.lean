-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_ThickSetMeanBounds_SZ_T3
-- name    : Formalism.LFunctionChainParameters.ThickSetMeanBounds.SZ.T3
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T09:07:50.068264+00:00
-- url     : https://prove2.me/theorems/f2561b55-a237-4cff-b6d6-19bb878a667f
-- title:
--   SZ: T3
-- statement:
--   The SZ construction uses the T3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/LipschitzWeightAndMinimum.lean#L53-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/LipschitzWeightAndMinimum.lean#L53-L75

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
open Formalism.LFunctionChainParameters.ThickSetMeanBounds.SZ

theorem Formalism.LFunctionChainParameters.ThickSetMeanBounds.SZ.T3 {x ε Y m n nT b : ℝ} (hx0 : 0 < x) (hm0 : 0 ≤ m) (hb : 0 ≤ b)
    (hY : Y = x ^ ((1 : ℝ) / 2 + 13 * ε / 8)) (hm2 : m ≤ x ^ ((1 : ℝ) / 2 + ε / 2))
    (hnT : x ^ (-(ε / 8)) * n / 2 ≤ nT) (hn : 0 ≤ n) :
    m * ((2 * n) * m * b * x ^ ε) ≤ 4 * Y * (nT * m * b) := by sorry
