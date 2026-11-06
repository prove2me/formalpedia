-- Prove2me | Theorems.Thm_BookProof_RelationShiftInvert_unitaryU_mem_relDomain
-- name    : BookProof.RelationShiftInvert.unitaryU_mem_relDomain
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-04T22:57:08.357718+00:00
-- url     : https://prove2.me/theorems/5ad57479-8b3b-4707-b89d-a0e868b59bd1
-- title:
--   `BookProof.RelationShiftInvert.unitaryU_mem_relDomain` (hT : IsNonnegSelfAdjoint T) (hsv : ∀ w : F, ((0 : F), w) ∈ T → w = 0) (x : relDomain T) (t : ℝ) : unitaryU hT hsv t (x : F)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterRelationShiftInvert`.
--
--   `BookProof.RelationShiftInvert.unitaryU_mem_relDomain` (hT : IsNonnegSelfAdjoint T) (hsv : ∀ w : F, ((0 : F), w) ∈ T → w = 0) (x : relDomain T) (t : ℝ) : unitaryU hT hsv t (x : F) ∈ relDomain T
--
--   Formalization note: Lean 4 identifier `BookProof.RelationShiftInvert.unitaryU_mem_relDomain`.

-- Generated from ChapterRelationShiftInvert.lean — theorem BookProof.RelationShiftInvert.unitaryU_mem_relDomain
import Definitions.Def_ChapterPositiveSquareRootUnique
import Definitions.Def_ChapterNonnegSquareRoot
import Definitions.Def_ChapterNonnegResolvent
import Definitions.Def_ChapterNonnegUnitaryGroup
import Definitions.Def_ChapterComplexShiftCore
import Mathlib
import Definitions.Def_ChapterRelationShiftInvert



open BookProof.PositiveSquareRoot
open BookProof.HashimotoShiftInvert
open BookProof.NonnegUnitaryGroup

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
variable {T T₁ T₂ : Submodule ℂ (F × F)}

theorem BookProof.RelationShiftInvert.unitaryU_mem_relDomain (hT : IsNonnegSelfAdjoint T)
    (hsv : ∀ w : F, ((0 : F), w) ∈ T → w = 0) (x : relDomain T) (t : ℝ) :
    unitaryU hT hsv t (x : F) ∈ relDomain T := by sorry
