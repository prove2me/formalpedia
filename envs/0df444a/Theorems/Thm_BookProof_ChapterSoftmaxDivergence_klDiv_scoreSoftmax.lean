-- Prove2me | Theorems.Thm_BookProof_ChapterSoftmaxDivergence_klDiv_scoreSoftmax
-- name    : BookProof.ChapterSoftmaxDivergence.klDiv_scoreSoftmax
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T23:16:02.554501+00:00
-- url     : https://prove2.me/theorems/a43df8ed-c58c-4420-a008-5dc7d4f1f9df
-- title:
--   `BookProof.ChapterSoftmaxDivergence.klDiv_scoreSoftmax` (beta gamma : ℝ) (s : Fin m → ℝ) (i : Fin m) : klDiv (scoreSoftmax beta s) (scoreSoftmax gamma s) = logPartition gamma s - l
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSoftmaxDivergence`.
--
--   `BookProof.ChapterSoftmaxDivergence.klDiv_scoreSoftmax` (beta gamma : ℝ) (s : Fin m → ℝ) (i : Fin m) : klDiv (scoreSoftmax beta s) (scoreSoftmax gamma s) = logPartition gamma s - logPartition beta s - (gamma - beta) * meanScore beta s
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSoftmaxDivergence.klDiv_scoreSoftmax`.

-- Generated from ChapterSoftmaxDivergence.lean — theorem BookProof.ChapterSoftmaxDivergence.klDiv_scoreSoftmax
import Definitions.Def_ChapterAttentionEntropy
import Mathlib
import Definitions.Def_ChapterSoftmaxDivergence
import Definitions.Def_ChapterSoftmaxSharpness
import Definitions.Def_ChapterSoftmaxFluctuation
open BookProof.ChapterSoftmaxSharpness
open BookProof.ChapterSoftmaxDivergence


open scoped BigOperators

noncomputable section


open BookProof.ChapterAttentionEntropy BookProof.ChapterSoftmaxSharpness
open BookProof.ChapterSoftmaxFluctuation

variable {m : ℕ}

theorem BookProof.ChapterSoftmaxDivergence.klDiv_scoreSoftmax (beta gamma : ℝ) (s : Fin m → ℝ) (i : Fin m) :
    klDiv (scoreSoftmax beta s) (scoreSoftmax gamma s)
      = logPartition gamma s - logPartition beta s
          - (gamma - beta) * meanScore beta s := by sorry
