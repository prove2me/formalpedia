-- Prove2me | Theorems.Thm_CompanionTheory_ThKR_LL_block_inl_inl_one
-- name    : CompanionTheory.ThKR.LL.block_inl_inl_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:31:05.247792+00:00
-- url     : https://prove2.me/theorems/d859a097-bdad-4bb6-86bc-b2951ba0f125
-- title:
--   LL: block inl inl one
-- statement:
--   The LL construction uses the block inl inl one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/ThickeningEstimates/LieGroupReduction/LocalLift.lean#L33-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/ThickeningEstimates/LieGroupReduction/LocalLift.lean#L33-L35

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

theorem CompanionTheory.ThKR.LL.block_inl_inl_one : bl Sum.inl Sum.inl (1 : Matrix (l ⊕ l) (l ⊕ l) ℝ) = 1 := by sorry
