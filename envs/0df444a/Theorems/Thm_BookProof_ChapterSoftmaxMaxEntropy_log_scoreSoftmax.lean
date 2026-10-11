-- Prove2me | Theorems.Thm_BookProof_ChapterSoftmaxMaxEntropy_log_scoreSoftmax
-- name    : BookProof.ChapterSoftmaxMaxEntropy.log_scoreSoftmax
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-11T08:15:51.455002+00:00
-- url     : https://prove2.me/theorems/ae8f2f12-b96f-4587-b02a-73c76ea9c4bf
-- title:
--   `BookProof.ChapterSoftmaxMaxEntropy.log_scoreSoftmax` (beta : ℝ) (s : Fin m → ℝ) (j : Fin m) : Real.log (scoreSoftmax beta s j) = beta * s j - logPartition beta s
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSoftmaxMaxEntropy`.
--
--   `BookProof.ChapterSoftmaxMaxEntropy.log_scoreSoftmax` (beta : ℝ) (s : Fin m → ℝ) (j : Fin m) : Real.log (scoreSoftmax beta s j) = beta * s j - logPartition beta s
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSoftmaxMaxEntropy.log_scoreSoftmax`.

-- Generated from ChapterSoftmaxMaxEntropy.lean — theorem BookProof.ChapterSoftmaxMaxEntropy.log_scoreSoftmax
import Definitions.Def_ChapterAttentionEntropy
import Mathlib
import Definitions.Def_ChapterSoftmaxMaxEntropy
import Definitions.Def_ChapterSoftmaxSharpness
import Definitions.Def_ChapterSoftmaxFluctuation
open BookProof.ChapterSoftmaxSharpness
open BookProof.ChapterSoftmaxMaxEntropy


open scoped BigOperators

noncomputable section


open BookProof.ChapterAttentionEntropy BookProof.ChapterSoftmaxSharpness
open BookProof.ChapterSoftmaxFluctuation

variable {m : ℕ}

theorem BookProof.ChapterSoftmaxMaxEntropy.log_scoreSoftmax (beta : ℝ) (s : Fin m → ℝ) (j : Fin m) :
    Real.log (scoreSoftmax beta s j) = beta * s j - logPartition beta s := by sorry
