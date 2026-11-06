-- Prove2me | Theorems.Thm_BookProof_RelationShiftInvert_isShiftInvert_invCLMAt
-- name    : BookProof.RelationShiftInvert.isShiftInvert_invCLMAt
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-04T22:58:54.361445+00:00
-- url     : https://prove2.me/theorems/7820aa16-f8c4-458a-b1ea-4edbe45adec4
-- title:
--   `BookProof.RelationShiftInvert.isShiftInvert_invCLMAt` (hT : IsNonnegSelfAdjoint T) (hsv : ∀ w : F, ((0 : F), w) ∈ T → w = 0) {γ : ℝ} (hγ : 0 < γ) : IsShiftInvert (relOp hsv) γ (in
-- statement:
--   Prove the following Lean 4 theorem from `ChapterRelationShiftInvert`.
--
--   `BookProof.RelationShiftInvert.isShiftInvert_invCLMAt` (hT : IsNonnegSelfAdjoint T) (hsv : ∀ w : F, ((0 : F), w) ∈ T → w = 0) {γ : ℝ} (hγ : 0 < γ) : IsShiftInvert (relOp hsv) γ (invCLMAt hT hγ)
--
--   Formalization note: Lean 4 identifier `BookProof.RelationShiftInvert.isShiftInvert_invCLMAt`.

-- Generated from ChapterRelationShiftInvert.lean — theorem BookProof.RelationShiftInvert.isShiftInvert_invCLMAt
import Definitions.Def_ChapterPositiveSquareRootUnique
import Definitions.Def_ChapterNonnegSquareRoot
import Definitions.Def_ChapterNonnegResolvent
import Definitions.Def_ChapterNonnegUnitaryGroup
import Definitions.Def_ChapterComplexShiftCore
import Mathlib
import Definitions.Def_ChapterRelationShiftInvert
import Definitions.Def_ChapterHashimotoShiftInvert
import Definitions.Def_ChapterQgOuterFockFarisLavine
import Definitions.Def_ChapterLeafGaps
open BookProof.QgOuterFockFL



open BookProof.PositiveSquareRoot
open BookProof.HashimotoShiftInvert
open BookProof.NonnegSquareRoot

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
variable {T T₁ T₂ : Submodule ℂ (F × F)}

theorem BookProof.RelationShiftInvert.isShiftInvert_invCLMAt (hT : IsNonnegSelfAdjoint T)
    (hsv : ∀ w : F, ((0 : F), w) ∈ T → w = 0) {γ : ℝ} (hγ : 0 < γ) :
    IsShiftInvert (relOp hsv) γ (invCLMAt hT hγ) := by sorry
