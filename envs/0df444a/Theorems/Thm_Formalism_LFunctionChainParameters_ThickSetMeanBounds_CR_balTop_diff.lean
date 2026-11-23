-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_ThickSetMeanBounds_CR_balTop_diff
-- name    : Formalism.LFunctionChainParameters.ThickSetMeanBounds.CR.balTop_diff
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T04:37:14.531928+00:00
-- url     : https://prove2.me/theorems/f14be2d8-f1d9-44fb-ba89-5d5306d70839
-- title:
--   CR: bal Top diff
-- statement:
--   The CR construction uses the bal Top diff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/LipschitzWeightAndMinimum.lean#L310-L329
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/LipschitzWeightAndMinimum.lean#L310-L329

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

theorem Formalism.LFunctionChainParameters.ThickSetMeanBounds.CR.balTop_diff (Hs : CycHost H) (a : ℝ) (t : H) (w w' : E0 × H → ℝ) (K : ℝ) (hK0 : 0 ≤ K)
    (hK : ∀ g, ¬ InPhi (g + topPl t) → ∀ ψ : AddChar (E0 × H) ℂ,
      ‖((w (cconj + g + topPl t) : ℝ) : ℂ) * GC Hs ψ (a / w (cconj + g + topPl t))
        - ((w' (cconj + g + topPl t) : ℝ) : ℂ) * GC Hs ψ (a / w' (cconj + g + topPl t))‖ ≤ K) :
    |balTop Hs a t w - balTop Hs a t w'| ≤ 2 * fPl H * K := by sorry
