-- Prove2me | Theorems.Thm_BookProof_RelationShiftInvert_hasDerivAt_unitaryU_relOp
-- name    : BookProof.RelationShiftInvert.hasDerivAt_unitaryU_relOp
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-11-04T22:57:06.462848+00:00
-- url     : https://prove2.me/theorems/1c09c616-28dd-4c74-9e02-99e6d12258df
-- title:
--   `BookProof.RelationShiftInvert.hasDerivAt_unitaryU_relOp` (hT : IsNonnegSelfAdjoint T) (hsv : ∀ w : F, ((0 : F), w) ∈ T → w = 0) (x : relDomain T) (t : ℝ) : HasDerivAt (fun s : ℝ =
-- statement:
--   Prove the following Lean 4 theorem from `ChapterRelationShiftInvert`.
--
--   `BookProof.RelationShiftInvert.hasDerivAt_unitaryU_relOp` (hT : IsNonnegSelfAdjoint T) (hsv : ∀ w : F, ((0 : F), w) ∈ T → w = 0) (x : relDomain T) (t : ℝ) : HasDerivAt (fun s : ℝ => unitaryU hT hsv s (x : F)) ((-Complex.I) • unitaryU hT hsv t (relOp hsv x)) t
--
--   Formalization note: Lean 4 identifier `BookProof.RelationShiftInvert.hasDerivAt_unitaryU_relOp`.

-- Generated from ChapterRelationShiftInvert.lean — theorem BookProof.RelationShiftInvert.hasDerivAt_unitaryU_relOp
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

theorem BookProof.RelationShiftInvert.hasDerivAt_unitaryU_relOp (hT : IsNonnegSelfAdjoint T)
    (hsv : ∀ w : F, ((0 : F), w) ∈ T → w = 0) (x : relDomain T) (t : ℝ) :
    HasDerivAt (fun s : ℝ => unitaryU hT hsv s (x : F))
      ((-Complex.I) • unitaryU hT hsv t (relOp hsv x)) t := by sorry
