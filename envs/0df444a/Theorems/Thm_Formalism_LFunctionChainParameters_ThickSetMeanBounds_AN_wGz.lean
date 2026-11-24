-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_ThickSetMeanBounds_AN_wGz
-- name    : Formalism.LFunctionChainParameters.ThickSetMeanBounds.AN.wGz
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T09:49:47.498253+00:00
-- url     : https://prove2.me/theorems/48cff3d0-a58d-42c8-a46a-1bb2a60d87d5
-- title:
--   AN: w Gz
-- statement:
--   The AN construction uses the w Gz property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/LipschitzWeightAndMinimum.lean#L879-L899
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/LipschitzWeightAndMinimum.lean#L879-L899

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

theorem Formalism.LFunctionChainParameters.ThickSetMeanBounds.AN.wGz (A w : ℝ) (hw : 0 < w) (M : ℕ) (hM : ⌊A / w⌋₊ ≤ M) :
    w * Gz (A / w) = ∑ n ∈ Icc 1 M, Λ n * max (A / n - w) 0 - A * Real.log (A / w)
      + (1 + Real.eulerMascheroniConstant) * A := by sorry
