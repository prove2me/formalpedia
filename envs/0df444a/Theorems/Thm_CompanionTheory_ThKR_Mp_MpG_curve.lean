-- Prove2me | Theorems.Thm_CompanionTheory_ThKR_Mp_MpG_curve
-- name    : CompanionTheory.ThKR.Mp.MpG.curve
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T23:27:22.480995+00:00
-- url     : https://prove2.me/theorems/bef0cc12-230b-4742-9007-6f22ebe1fcd3
-- title:
--   Mp G: curve
-- statement:
--   The Mp G construction uses the curve property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/ThickeningEstimates/LieGroupReduction/MetaplecticRepresentation/HasFDerivAtOfCurves.lean#L81-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/ThickeningEstimates/LieGroupReduction/MetaplecticRepresentation/HasFDerivAtOfCurves.lean#L81-L126

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
variable {l : Type} [Fintype l] [DecidableEq l]

theorem CompanionTheory.ThKR.Mp.MpG.curve {g : ℝ → (l ⊕ l) → (l ⊕ l) → ℝ} {X : (l ⊕ l) → (l ⊕ l) → ℝ} (g0 : Matrix.of (g 0) = 1)
    (hg : HasDerivAt g X 0) (f : Sch l) :
    HasDerivAt (fun t => schwartzToL2 l (sec (Matrix.of (g t)) f)) (schwartzToL2 l (Qd (Matrix.of X) f)) 0 := by sorry
