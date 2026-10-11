-- Prove2me | Theorems.Thm_BookProof_ChapterSoftmaxMaxEntropy_crossEntropy_scoreSoftmax
-- name    : BookProof.ChapterSoftmaxMaxEntropy.crossEntropy_scoreSoftmax
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-11T00:08:08.149702+00:00
-- url     : https://prove2.me/theorems/6ff6c19d-a8df-4ad3-847d-fad21ca7f6e6
-- title:
--   `BookProof.ChapterSoftmaxMaxEntropy.crossEntropy_scoreSoftmax` (beta : ℝ) (s : Fin m → ℝ) {p : Fin m → ℝ} (hpsum : ∑ j, p j = 1) : crossEntropy p (scoreSoftmax beta s) = logPartiti
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSoftmaxMaxEntropy`.
--
--   `BookProof.ChapterSoftmaxMaxEntropy.crossEntropy_scoreSoftmax` (beta : ℝ) (s : Fin m → ℝ) {p : Fin m → ℝ} (hpsum : ∑ j, p j = 1) : crossEntropy p (scoreSoftmax beta s) = logPartition beta s - beta * ∑ j, p j * s j
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSoftmaxMaxEntropy.crossEntropy_scoreSoftmax`.

-- Generated from ChapterSoftmaxMaxEntropy.lean — theorem BookProof.ChapterSoftmaxMaxEntropy.crossEntropy_scoreSoftmax
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

theorem BookProof.ChapterSoftmaxMaxEntropy.crossEntropy_scoreSoftmax (beta : ℝ) (s : Fin m → ℝ) {p : Fin m → ℝ}
    (hpsum : ∑ j, p j = 1) :
    crossEntropy p (scoreSoftmax beta s) = logPartition beta s - beta * ∑ j, p j * s j := by sorry
