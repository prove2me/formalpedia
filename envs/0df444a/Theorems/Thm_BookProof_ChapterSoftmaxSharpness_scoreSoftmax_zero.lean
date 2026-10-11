-- Prove2me | Theorems.Thm_BookProof_ChapterSoftmaxSharpness_scoreSoftmax_zero
-- name    : BookProof.ChapterSoftmaxSharpness.scoreSoftmax_zero
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T14:36:39.202764+00:00
-- url     : https://prove2.me/theorems/f3e1364e-54ab-4f9d-a813-c8be5a8a4a60
-- title:
--   `BookProof.ChapterSoftmaxSharpness.scoreSoftmax_zero` (s : Fin m → ℝ) (j : Fin m) : scoreSoftmax 0 s j = 1 / m
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSoftmaxSharpness`.
--
--   `BookProof.ChapterSoftmaxSharpness.scoreSoftmax_zero` (s : Fin m → ℝ) (j : Fin m) : scoreSoftmax 0 s j = 1 / m
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSoftmaxSharpness.scoreSoftmax_zero`.

-- Generated from ChapterSoftmaxSharpness.lean — theorem BookProof.ChapterSoftmaxSharpness.scoreSoftmax_zero
import Definitions.Def_ChapterSoftmaxBorn
import Mathlib
import Definitions.Def_ChapterSoftmaxSharpness
open BookProof.ChapterSoftmaxSharpness


open scoped BigOperators

noncomputable section


open Filter Topology BookProof.ChapterSoftmaxBorn

variable {n m : ℕ}

theorem BookProof.ChapterSoftmaxSharpness.scoreSoftmax_zero (s : Fin m → ℝ) (j : Fin m) :
    scoreSoftmax 0 s j = 1 / m := by sorry
