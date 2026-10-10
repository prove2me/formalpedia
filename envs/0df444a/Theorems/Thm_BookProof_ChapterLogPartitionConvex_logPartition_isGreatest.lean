-- Prove2me | Theorems.Thm_BookProof_ChapterLogPartitionConvex_logPartition_isGreatest
-- name    : BookProof.ChapterLogPartitionConvex.logPartition_isGreatest
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-09T12:33:31.376505+00:00
-- url     : https://prove2.me/theorems/ba936635-2bb4-480f-9764-daabb4302b7c
-- title:
--   `BookProof.ChapterLogPartitionConvex.logPartition_isGreatest` (beta : ℝ) (s : Fin m → ℝ) (i : Fin m) : IsGreatest {x : ℝ | ∃ p : Fin m → ℝ, (∀ j, 0 ≤ p j) ∧ (∑ j, p j) = 1...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterLogPartitionConvex`.
--
--   `BookProof.ChapterLogPartitionConvex.logPartition_isGreatest` (beta : ℝ) (s : Fin m → ℝ) (i : Fin m) : IsGreatest {x : ℝ | ∃ p : Fin m → ℝ, (∀ j, 0 ≤ p j) ∧ (∑ j, p j) = 1 ∧ x = beta * (∑ j, p j * s j) + shannonEntropy p} (logPartition beta s)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterLogPartitionConvex.logPartition_isGreatest`.

-- Generated from ChapterLogPartitionConvex.lean — theorem BookProof.ChapterLogPartitionConvex.logPartition_isGreatest
import Definitions.Def_ChapterAttentionEntropy
import Mathlib
import Definitions.Def_ChapterLogPartitionConvex
import Definitions.Def_ChapterSoftmaxSharpness
import Definitions.Def_ChapterSoftmaxFluctuation
open BookProof.ChapterSoftmaxSharpness
open BookProof.ChapterLogPartitionConvex


open scoped BigOperators

noncomputable section


open BookProof.ChapterAttentionEntropy BookProof.ChapterSoftmaxSharpness
open BookProof.ChapterSoftmaxFluctuation

variable {m : ℕ}

theorem BookProof.ChapterLogPartitionConvex.logPartition_isGreatest (beta : ℝ) (s : Fin m → ℝ) (i : Fin m) :
    IsGreatest {x : ℝ | ∃ p : Fin m → ℝ, (∀ j, 0 ≤ p j) ∧ (∑ j, p j) = 1 ∧
        x = beta * (∑ j, p j * s j) + shannonEntropy p} (logPartition beta s) := by sorry
