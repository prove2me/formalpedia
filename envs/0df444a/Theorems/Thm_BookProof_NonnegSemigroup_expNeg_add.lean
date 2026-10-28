-- Prove2me | Theorems.Thm_BookProof_NonnegSemigroup_expNeg_add
-- name    : BookProof.NonnegSemigroup.expNeg_add
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-25T14:35:41.902643+00:00
-- url     : https://prove2.me/theorems/1ebb6435-4cfb-4120-b6ef-9930d38eac5b
-- title:
--   `BookProof.NonnegSemigroup.expNeg_add` (A : F →L[ℂ] F) (s t : ℝ) : expNeg A (s + t) = expNeg A s * expNeg A t
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNonnegSemigroup`.
--
--   `BookProof.NonnegSemigroup.expNeg_add` (A : F →L[ℂ] F) (s t : ℝ) : expNeg A (s + t) = expNeg A s * expNeg A t
--
--   Formalization note: Lean 4 identifier `BookProof.NonnegSemigroup.expNeg_add`.

-- Generated from ChapterNonnegSemigroup.lean — theorem BookProof.NonnegSemigroup.expNeg_add
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

theorem BookProof.NonnegSemigroup.expNeg_add (A : F →L[ℂ] F) (s t : ℝ) :
    expNeg A (s + t) = expNeg A s * expNeg A t := by sorry
