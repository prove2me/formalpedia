-- Prove2me | Theorems.Thm_CompanionTheory_ThKR_LL_differentiableAt_det
-- name    : CompanionTheory.ThKR.LL.differentiableAt_det
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:18:01.426936+00:00
-- url     : https://prove2.me/theorems/18f4f18d-c6f6-405e-a1af-8312f43d8835
-- title:
--   LL: differentiable At det
-- statement:
--   The LL construction uses the differentiable At det property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/ThickeningEstimates/LieGroupReduction/LocalLift.lean#L142-L145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/ThickeningEstimates/LieGroupReduction/LocalLift.lean#L142-L145

import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_NormExpSubLe
import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_LocalLift
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil CompanionTheory.ThKF.E Filter Topology LineDeriv
open scoped Real RealInnerProductSpace FourierTransform
open CompanionTheory CompanionTheory.ThKR CompanionTheory.ThKR.LL
variable {l : Type} [Fintype l] [DecidableEq l]

theorem CompanionTheory.ThKR.LL.differentiableAt_det {M : ℝ → Matrix l l ℝ} {t : ℝ} (h : ∀ i j, DifferentiableAt ℝ (fun t => M t i j) t) :
    DifferentiableAt ℝ (fun t => (M t).det) t := by sorry
