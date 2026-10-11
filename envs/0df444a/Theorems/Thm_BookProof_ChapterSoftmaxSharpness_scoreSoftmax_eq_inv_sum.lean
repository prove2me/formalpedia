-- Prove2me | Theorems.Thm_BookProof_ChapterSoftmaxSharpness_scoreSoftmax_eq_inv_sum
-- name    : BookProof.ChapterSoftmaxSharpness.scoreSoftmax_eq_inv_sum
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T14:36:39.162363+00:00
-- url     : https://prove2.me/theorems/287af04d-162e-4e54-9889-bf73611ca939
-- title:
--   `BookProof.ChapterSoftmaxSharpness.scoreSoftmax_eq_inv_sum` (beta : ℝ) (s : Fin m → ℝ) (j : Fin m) : scoreSoftmax beta s j = 1 / ∑ l, Real.exp (beta * (s l - s j))
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSoftmaxSharpness`.
--
--   `BookProof.ChapterSoftmaxSharpness.scoreSoftmax_eq_inv_sum` (beta : ℝ) (s : Fin m → ℝ) (j : Fin m) : scoreSoftmax beta s j = 1 / ∑ l, Real.exp (beta * (s l - s j))
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSoftmaxSharpness.scoreSoftmax_eq_inv_sum`.

-- Generated from ChapterSoftmaxSharpness.lean — theorem BookProof.ChapterSoftmaxSharpness.scoreSoftmax_eq_inv_sum
import Definitions.Def_ChapterSoftmaxBorn
import Mathlib
import Definitions.Def_ChapterSoftmaxSharpness
open BookProof.ChapterSoftmaxSharpness


open scoped BigOperators

noncomputable section


open Filter Topology BookProof.ChapterSoftmaxBorn

variable {n m : ℕ}

theorem BookProof.ChapterSoftmaxSharpness.scoreSoftmax_eq_inv_sum (beta : ℝ) (s : Fin m → ℝ) (j : Fin m) :
    scoreSoftmax beta s j = 1 / ∑ l, Real.exp (beta * (s l - s j)) := by sorry
