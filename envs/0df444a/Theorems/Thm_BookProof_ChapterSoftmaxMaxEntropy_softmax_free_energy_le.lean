-- Prove2me | Theorems.Thm_BookProof_ChapterSoftmaxMaxEntropy_softmax_free_energy_le
-- name    : BookProof.ChapterSoftmaxMaxEntropy.softmax_free_energy_le
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-11T20:10:26.314286+00:00
-- url     : https://prove2.me/theorems/76fd1385-3dc3-4fe2-a745-f73d7df21664
-- title:
--   `BookProof.ChapterSoftmaxMaxEntropy.softmax_free_energy_le` (beta : ℝ) (s : Fin m → ℝ) (i : Fin m) {p : Fin m → ℝ} (hp0 : ∀ j, 0 ≤ p j) (hpsum : ∑ j, p j = 1) : -logPartition beta
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSoftmaxMaxEntropy`.
--
--   `BookProof.ChapterSoftmaxMaxEntropy.softmax_free_energy_le` (beta : ℝ) (s : Fin m → ℝ) (i : Fin m) {p : Fin m → ℝ} (hp0 : ∀ j, 0 ≤ p j) (hpsum : ∑ j, p j = 1) : -logPartition beta s ≤ -(beta * ∑ j, p j * s j) - shannonEntropy p
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSoftmaxMaxEntropy.softmax_free_energy_le`.

-- Generated from ChapterSoftmaxMaxEntropy.lean — theorem BookProof.ChapterSoftmaxMaxEntropy.softmax_free_energy_le
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

theorem BookProof.ChapterSoftmaxMaxEntropy.softmax_free_energy_le (beta : ℝ) (s : Fin m → ℝ) (i : Fin m)
    {p : Fin m → ℝ} (hp0 : ∀ j, 0 ≤ p j) (hpsum : ∑ j, p j = 1) :
    -logPartition beta s ≤ -(beta * ∑ j, p j * s j) - shannonEntropy p := by sorry
