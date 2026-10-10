-- Prove2me | Theorems.Thm_BookProof_ChapterNumericalRangeSemigroup_hasDerivAt_expApply
-- name    : BookProof.ChapterNumericalRangeSemigroup.hasDerivAt_expApply
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T08:16:14.055145+00:00
-- url     : https://prove2.me/theorems/5c73a0d1-44f4-48b2-824a-8618ec90246e
-- title:
--   `BookProof.ChapterNumericalRangeSemigroup.hasDerivAt_expApply` (A : E →L[ℂ] E) (x : E) (t : ℝ) : HasDerivAt (fun s : ℝ => (NormedSpace.exp (s • A)) x) (A (NormedSpace.exp (t • A) x
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNumericalRangeSemigroup`.
--
--   `BookProof.ChapterNumericalRangeSemigroup.hasDerivAt_expApply` (A : E →L[ℂ] E) (x : E) (t : ℝ) : HasDerivAt (fun s : ℝ => (NormedSpace.exp (s • A)) x) (A (NormedSpace.exp (t • A) x)) t
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterNumericalRangeSemigroup.hasDerivAt_expApply`.

-- Generated from ChapterNumericalRangeSemigroup.lean — theorem BookProof.ChapterNumericalRangeSemigroup.hasDerivAt_expApply
import Mathlib
import Definitions.Def_ChapterNumericalRangeSemigroup
open BookProof.ChapterNumericalRangeSemigroup


open scoped InnerProductSpace


variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem BookProof.ChapterNumericalRangeSemigroup.hasDerivAt_expApply (A : E →L[ℂ] E) (x : E) (t : ℝ) :
    HasDerivAt (fun s : ℝ => (NormedSpace.exp (s • A)) x) (A (NormedSpace.exp (t • A) x)) t := by sorry
