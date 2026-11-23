-- Prove2me | Theorems.Thm_CompanionTheory_ThKR_LL_det_bl
-- name    : CompanionTheory.ThKR.LL.det_bl
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:30:37.763342+00:00
-- url     : https://prove2.me/theorems/ab07e14f-8cb9-4107-8e64-f2c570adde81
-- title:
--   LL: det bl
-- statement:
--   The LL construction uses the det bl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/ThickeningEstimates/LieGroupReduction/LocalLift.lean#L30-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/ThickeningEstimates/LieGroupReduction/LocalLift.lean#L30-L31

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

theorem CompanionTheory.ThKR.LL.det_bl (i j : l → l ⊕ l) (g : Matrix (l ⊕ l) (l ⊕ l) ℝ) : (bl i j g).det = (g.submatrix i j).det := by sorry
