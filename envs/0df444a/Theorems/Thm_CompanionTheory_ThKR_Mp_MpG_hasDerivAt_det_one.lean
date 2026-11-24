-- Prove2me | Theorems.Thm_CompanionTheory_ThKR_Mp_MpG_hasDerivAt_det_one
-- name    : CompanionTheory.ThKR.Mp.MpG.hasDerivAt_det_one
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T23:27:32.536603+00:00
-- url     : https://prove2.me/theorems/c41099ea-c706-4eea-b026-5507159e38e7
-- title:
--   Mp G: has Deriv At det one
-- statement:
--   The Mp G construction uses the has Deriv At det one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/ThickeningEstimates/LieGroupReduction/MetaplecticRepresentation/HasFDerivAtOfCurves.lean#L61-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/ThickeningEstimates/LieGroupReduction/MetaplecticRepresentation/HasFDerivAtOfCurves.lean#L61-L79

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

theorem CompanionTheory.ThKR.Mp.MpG.hasDerivAt_det_one {M : ℝ → l → l → ℝ} {X : l → l → ℝ} (h : HasDerivAt M X 0) (h0 : Matrix.of (M 0) = 1) :
    HasDerivAt (fun t => (Matrix.of (M t)).det) (Matrix.of X).trace 0 := by sorry
