-- Prove2me | Theorems.Thm_CompanionTheory_ThKR_LL_bl_apply
-- name    : CompanionTheory.ThKR.LL.bl_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:30:37.175031+00:00
-- url     : https://prove2.me/theorems/5731d89d-ac2e-4c9b-9bb6-2d9d4cc92096
-- title:
--   LL: bl apply
-- statement:
--   The LL construction uses the bl apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/ThickeningEstimates/LieGroupReduction/LocalLift.lean#L17-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/ThickeningEstimates/LieGroupReduction/LocalLift.lean#L17-L18

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

theorem CompanionTheory.ThKR.LL.bl_apply (i j : l → l ⊕ l) (g : Matrix (l ⊕ l) (l ⊕ l) ℝ) (x : Eu l) (a : l) :
    bl i j g x a = ∑ b, g (i a) (j b) * x b := by sorry
