-- Prove2me | Theorems.Thm_BookProof_RelationShiftInvert_relOp_unitaryU
-- name    : BookProof.RelationShiftInvert.relOp_unitaryU
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-05T19:58:09.610361+00:00
-- url     : https://prove2.me/theorems/73f9e00a-8db9-40e8-926f-75d500f87e1b
-- title:
--   `BookProof.RelationShiftInvert.relOp_unitaryU` (hT : IsNonnegSelfAdjoint T) (hsv : ∀ w : F, ((0 : F), w) ∈ T → w = 0) (x : relDomain T) (t : ℝ) : relOp hsv ⟨unitaryU hT hsv t (x :
-- statement:
--   Prove the following Lean 4 theorem from `ChapterRelationShiftInvert`.
--
--   `BookProof.RelationShiftInvert.relOp_unitaryU` (hT : IsNonnegSelfAdjoint T) (hsv : ∀ w : F, ((0 : F), w) ∈ T → w = 0) (x : relDomain T) (t : ℝ) : relOp hsv ⟨unitaryU hT hsv t (x : F), unitaryU_mem_relDomain hT hsv x t⟩ = unitaryU hT hsv t (relOp hsv x)
--
--   Formalization note: Lean 4 identifier `BookProof.RelationShiftInvert.relOp_unitaryU`.

-- Generated from ChapterRelationShiftInvert.lean — theorem BookProof.RelationShiftInvert.relOp_unitaryU
import Definitions.Def_ChapterPositiveSquareRootUnique
import Definitions.Def_ChapterNonnegSquareRoot
import Definitions.Def_ChapterNonnegResolvent
import Definitions.Def_ChapterNonnegUnitaryGroup
import Definitions.Def_ChapterComplexShiftCore
import Mathlib
import Definitions.Def_ChapterRelationShiftInvert
import Theorems.Thm_BookProof_RelationShiftInvert_unitaryU_mem_relDomain
open BookProof.NonnegUnitaryGroup
open BookProof.RelationShiftInvert



open BookProof.PositiveSquareRoot
open BookProof.HashimotoShiftInvert

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
variable {T T₁ T₂ : Submodule ℂ (F × F)}

theorem BookProof.RelationShiftInvert.relOp_unitaryU (hT : IsNonnegSelfAdjoint T)
    (hsv : ∀ w : F, ((0 : F), w) ∈ T → w = 0) (x : relDomain T) (t : ℝ) :
    relOp hsv ⟨unitaryU hT hsv t (x : F), unitaryU_mem_relDomain hT hsv x t⟩
      = unitaryU hT hsv t (relOp hsv x) := by sorry
