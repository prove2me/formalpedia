-- Prove2me | Theorems.Thm_CompanionTheory_ThKR_Mp_MpG_hasFDerivAt_of_curves
-- name    : CompanionTheory.ThKR.Mp.MpG.hasFDerivAt_of_curves
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T23:26:20.593126+00:00
-- url     : https://prove2.me/theorems/0ecc1183-ab0f-4b05-9d4b-a9c90405ced8
-- title:
--   Mp G: has FDeriv At of curves
-- statement:
--   The Mp G construction uses the has FDeriv At of curves property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/ThickeningEstimates/LieGroupReduction/MetaplecticRepresentation/HasFDerivAtOfCurves.lean#L10-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/ThickeningEstimates/LieGroupReduction/MetaplecticRepresentation/HasFDerivAtOfCurves.lean#L10-L57

import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_MetaplecticRepresentation_MpFOne
import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_MetaplecticRepresentation_HasFDerivAtOfCurves
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil CompanionTheory.ThKF.E Filter Topology CompanionTheory.ThKR.LL
open scoped Real ContDiff
open CompanionTheory CompanionTheory.ThKR CompanionTheory.ThKR.Mp CompanionTheory.ThKR.Mp.MpG

theorem CompanionTheory.ThKR.Mp.MpG.hasFDerivAt_of_curves {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] {Φ : E → F} {L : E →L[ℝ] F} {x₀ : E}
    (h : ∀ (c : ℝ → E) (v : E), c 0 = x₀ → HasDerivAt c v 0 → HasDerivAt (fun t => Φ (c t)) (L v) 0) :
    HasFDerivAt Φ L x₀ := by sorry
