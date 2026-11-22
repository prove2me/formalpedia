-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_ThickSetMeanBounds_CR_norm_avg_le
-- name    : Formalism.LFunctionChainParameters.ThickSetMeanBounds.CR.norm_avg_le
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T22:56:41.308689+00:00
-- url     : https://prove2.me/theorems/94c665b7-ee39-4f7e-b45a-9e2c45103cf4
-- title:
--   CR: norm avg le
-- statement:
--   The CR construction uses the norm avg le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/LipschitzWeightAndMinimum.lean#L188-L212
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/LipschitzWeightAndMinimum.lean#L188-L212

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

theorem Formalism.LFunctionChainParameters.ThickSetMeanBounds.CR.norm_avg_le (S : Finset (E0 × H)) (hS : (S.card : ℝ) ≤ fPl H) (F : E0 × H → AddChar (E0 × H) ℂ → ℂ)
    (K : ℝ) (hK0 : 0 ≤ K) (hK : ∀ g ∈ S, ∀ ψ, ‖F g ψ‖ ≤ K) :
    ‖(1 / ((PhiSet (H := H)).card : ℂ)) * ∑ g ∈ S, ∑ ψ : AddChar (E0 × H) ℂ, ψ (-g) * F g ψ‖
      ≤ 2 * fPl H * K := by sorry
