-- Prove2me | Theorems.Thm_BookProof_NonnegSemigroup_isSelfAdjoint_expNeg
-- name    : BookProof.NonnegSemigroup.isSelfAdjoint_expNeg
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-25T14:34:06.200923+00:00
-- url     : https://prove2.me/theorems/5959e8fb-d6bd-44d6-8a2d-346670711145
-- title:
--   `BookProof.NonnegSemigroup.isSelfAdjoint_expNeg` {A : F →L[ℂ] F} (hA : IsSelfAdjoint A) (t : ℝ) : IsSelfAdjoint (expNeg A t)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNonnegSemigroup`.
--
--   `BookProof.NonnegSemigroup.isSelfAdjoint_expNeg` {A : F →L[ℂ] F} (hA : IsSelfAdjoint A) (t : ℝ) : IsSelfAdjoint (expNeg A t)
--
--   Formalization note: Lean 4 identifier `BookProof.NonnegSemigroup.isSelfAdjoint_expNeg`.

-- Generated from ChapterNonnegSemigroup.lean — theorem BookProof.NonnegSemigroup.isSelfAdjoint_expNeg
import Definitions.Def_ChapterClosureUniqueness
import Definitions.Def_ChapterPositiveSquareRootUnique
import Definitions.Def_ChapterNonnegResolvent
import Definitions.Def_ChapterNonnegUnitaryGroup
import Mathlib
import Definitions.Def_ChapterNonnegSemigroup



open BookProof.ClosureUniqueness
open Filter Topology NormedSpace
open scoped InnerProductSpace

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem BookProof.NonnegSemigroup.isSelfAdjoint_expNeg {A : F →L[ℂ] F} (hA : IsSelfAdjoint A) (t : ℝ) :
    IsSelfAdjoint (expNeg A t) := by sorry
