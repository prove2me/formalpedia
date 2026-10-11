-- Prove2me | Theorems.Thm_BookProof_ChapterSoftmaxSharpness_softmax_eq_scoreSoftmax
-- name    : BookProof.ChapterSoftmaxSharpness.softmax_eq_scoreSoftmax
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T14:36:49.787425+00:00
-- url     : https://prove2.me/theorems/6ae59cf2-a483-49d6-9102-320270584ec8
-- title:
--   `BookProof.ChapterSoftmaxSharpness.softmax_eq_scoreSoftmax` (beta : ℝ) (q : EuclideanSpace ℝ (Fin n)) (k : Fin m → EuclideanSpace ℝ (Fin n)) (j : Fin m) : softmax beta q k j = scor
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSoftmaxSharpness`.
--
--   `BookProof.ChapterSoftmaxSharpness.softmax_eq_scoreSoftmax` (beta : ℝ) (q : EuclideanSpace ℝ (Fin n)) (k : Fin m → EuclideanSpace ℝ (Fin n)) (j : Fin m) : softmax beta q k j = scoreSoftmax beta (fun l => inner ℝ q (k l)) j
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSoftmaxSharpness.softmax_eq_scoreSoftmax`.

-- Generated from ChapterSoftmaxSharpness.lean — theorem BookProof.ChapterSoftmaxSharpness.softmax_eq_scoreSoftmax
import Mathlib
import Definitions.Def_ChapterSoftmaxSharpness
import Definitions.Def_ChapterSoftmaxBorn
open BookProof.ChapterSoftmaxBorn
open BookProof.ChapterSoftmaxSharpness


open scoped BigOperators

noncomputable section


open Filter Topology BookProof.ChapterSoftmaxBorn

variable {n m : ℕ}

theorem BookProof.ChapterSoftmaxSharpness.softmax_eq_scoreSoftmax (beta : ℝ) (q : EuclideanSpace ℝ (Fin n))
    (k : Fin m → EuclideanSpace ℝ (Fin n)) (j : Fin m) :
    softmax beta q k j = scoreSoftmax beta (fun l => inner ℝ q (k l)) j := by sorry
