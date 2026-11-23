-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_ThickSetMeanBounds_CR_mean_le
-- name    : Formalism.LFunctionChainParameters.ThickSetMeanBounds.CR.mean_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:36:55.697822+00:00
-- url     : https://prove2.me/theorems/444dc552-c831-422e-8b10-23a410c04afc
-- title:
--   CR: mean le
-- statement:
--   The CR construction uses the mean le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/LipschitzWeightAndMinimum.lean#L226-L242
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/LipschitzWeightAndMinimum.lean#L226-L242

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

theorem Formalism.LFunctionChainParameters.ThickSetMeanBounds.CR.mean_le {m : ℕ} (TT : Finset H) (F G : H → H → Fin m → ℝ) (K : ℝ)
    (h : ∀ u0, ∀ t ∈ TT, ∀ j, F u0 t j ≤ G u0 t j + K) :
    (1 / (Fintype.card H : ℝ)) * ∑ u0 : H, ∑ t ∈ TT, ∑ j : Fin m, F u0 t j
      ≤ (1 / (Fintype.card H : ℝ)) * (∑ u0 : H, ∑ t ∈ TT, ∑ j : Fin m, G u0 t j) + (TT.card : ℝ) * m * K := by sorry
