-- Prove2me | Theorems.Thm_CompanionTheory_ThKR_Mp_J_mul_transpose_inl
-- name    : CompanionTheory.ThKR.Mp.J_mul_transpose_inl
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T23:17:05.481706+00:00
-- url     : https://prove2.me/theorems/56b15904-9581-4705-8962-37254026ed5f
-- title:
--   Mp: J mul transpose inl
-- statement:
--   The Mp construction uses the J mul transpose inl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/ThickeningEstimates/LieGroupReduction/MetaplecticRepresentation/MetaplecticUnipotentBlockSecondDiag.lean#L12-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/ThickeningEstimates/LieGroupReduction/MetaplecticRepresentation/MetaplecticUnipotentBlockSecondDiag.lean#L12-L14

import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_MetaplecticRepresentation_ContinuousOm
import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_MetaplecticRepresentation_MetaplecticUnipotentBlockSecondDiag
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil CompanionTheory.ThKF.E Filter Topology CompanionTheory.ThKR.LL LineDeriv
open scoped Real RealInnerProductSpace FourierTransform
open CompanionTheory CompanionTheory.ThKR CompanionTheory.ThKR.Mp
variable {l : Type} [Fintype l] [DecidableEq l]

theorem CompanionTheory.ThKR.Mp.J_mul_transpose_inl (s : Mat l) (a : l) (j : l ⊕ l) :
    (Matrix.J l ℝ * sᵀ) (.inl a) j = -s j (.inr a) := by sorry
