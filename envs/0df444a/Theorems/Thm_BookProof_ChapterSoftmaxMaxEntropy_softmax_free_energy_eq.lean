-- Prove2me | Theorems.Thm_BookProof_ChapterSoftmaxMaxEntropy_softmax_free_energy_eq
-- name    : BookProof.ChapterSoftmaxMaxEntropy.softmax_free_energy_eq
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-11T08:16:11.289992+00:00
-- url     : https://prove2.me/theorems/074320c2-32bf-4f77-b9e6-b18028d60ff5
-- title:
--   `BookProof.ChapterSoftmaxMaxEntropy.softmax_free_energy_eq` (beta : ℝ) (s : Fin m → ℝ) (i : Fin m) : -(beta * ∑ j, scoreSoftmax beta s j * s j) - shannonEntropy (scoreSoftmax beta
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSoftmaxMaxEntropy`.
--
--   `BookProof.ChapterSoftmaxMaxEntropy.softmax_free_energy_eq` (beta : ℝ) (s : Fin m → ℝ) (i : Fin m) : -(beta * ∑ j, scoreSoftmax beta s j * s j) - shannonEntropy (scoreSoftmax beta s) = -logPartition beta s
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSoftmaxMaxEntropy.softmax_free_energy_eq`.

-- Generated from ChapterSoftmaxMaxEntropy.lean — theorem BookProof.ChapterSoftmaxMaxEntropy.softmax_free_energy_eq
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

theorem BookProof.ChapterSoftmaxMaxEntropy.softmax_free_energy_eq (beta : ℝ) (s : Fin m → ℝ) (i : Fin m) :
    -(beta * ∑ j, scoreSoftmax beta s j * s j) - shannonEntropy (scoreSoftmax beta s)
      = -logPartition beta s := by sorry
