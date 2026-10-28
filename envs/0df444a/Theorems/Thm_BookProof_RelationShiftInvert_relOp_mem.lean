-- Prove2me | Theorems.Thm_BookProof_RelationShiftInvert_relOp_mem
-- name    : BookProof.RelationShiftInvert.relOp_mem
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-27T05:39:23.593546+00:00
-- url     : https://prove2.me/theorems/a83f7609-20ad-41f2-acec-0e47ade2c2d5
-- title:
--   `BookProof.RelationShiftInvert.relOp_mem` (hsv : ∀ w : F, ((0 : F), w) ∈ T → w = 0) (x : relDomain T) : ((x : F), relOp hsv x) ∈ T
-- statement:
--   Prove the following Lean 4 theorem from `ChapterRelationShiftInvert`.
--
--   `BookProof.RelationShiftInvert.relOp_mem` (hsv : ∀ w : F, ((0 : F), w) ∈ T → w = 0) (x : relDomain T) : ((x : F), relOp hsv x) ∈ T
--
--   Formalization note: Lean 4 identifier `BookProof.RelationShiftInvert.relOp_mem`.

-- Generated from ChapterRelationShiftInvert.lean — theorem BookProof.RelationShiftInvert.relOp_mem
import Definitions.Def_ChapterPositiveSquareRootUnique
import Definitions.Def_ChapterNonnegSquareRoot
import Definitions.Def_ChapterNonnegResolvent
import Definitions.Def_ChapterNonnegUnitaryGroup
import Definitions.Def_ChapterComplexShiftCore
import Mathlib
import Definitions.Def_ChapterRelationShiftInvert



open BookProof.PositiveSquareRoot
open BookProof.HashimotoShiftInvert

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
variable {T T₁ T₂ : Submodule ℂ (F × F)}

theorem BookProof.RelationShiftInvert.relOp_mem (hsv : ∀ w : F, ((0 : F), w) ∈ T → w = 0) (x : relDomain T) :
    ((x : F), relOp hsv x) ∈ T := by sorry
