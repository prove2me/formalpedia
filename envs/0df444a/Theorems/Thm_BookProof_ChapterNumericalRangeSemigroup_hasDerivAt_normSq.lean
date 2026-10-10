-- Prove2me | Theorems.Thm_BookProof_ChapterNumericalRangeSemigroup_hasDerivAt_normSq
-- name    : BookProof.ChapterNumericalRangeSemigroup.hasDerivAt_normSq
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T08:17:02.960219+00:00
-- url     : https://prove2.me/theorems/b20945d2-25e2-4d30-876a-6e172e9305c3
-- title:
--   `BookProof.ChapterNumericalRangeSemigroup.hasDerivAt_normSq` (A : E →L[ℂ] E) (x : E) (t : ℝ) : HasDerivAt (fun s : ℝ => ‖(NormedSpace.exp (s • A)) x‖ ^ 2) (2 * (inner ℂ (NormedSpac
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNumericalRangeSemigroup`.
--
--   `BookProof.ChapterNumericalRangeSemigroup.hasDerivAt_normSq` (A : E →L[ℂ] E) (x : E) (t : ℝ) : HasDerivAt (fun s : ℝ => ‖(NormedSpace.exp (s • A)) x‖ ^ 2) (2 * (inner ℂ (NormedSpace.exp (t • A) x) (A (NormedSpace.exp (t • A) x))).re) t
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterNumericalRangeSemigroup.hasDerivAt_normSq`.

-- Generated from ChapterNumericalRangeSemigroup.lean — theorem BookProof.ChapterNumericalRangeSemigroup.hasDerivAt_normSq
import Mathlib
import Definitions.Def_ChapterNumericalRangeSemigroup
open BookProof.ChapterNumericalRangeSemigroup


open scoped InnerProductSpace


variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem BookProof.ChapterNumericalRangeSemigroup.hasDerivAt_normSq (A : E →L[ℂ] E) (x : E) (t : ℝ) :
    HasDerivAt (fun s : ℝ => ‖(NormedSpace.exp (s • A)) x‖ ^ 2)
      (2 * (inner ℂ (NormedSpace.exp (t • A) x) (A (NormedSpace.exp (t • A) x))).re) t := by sorry
