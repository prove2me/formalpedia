-- Prove2me | Theorems.Thm_BookProof_ChapterLogPartitionConvex_differentiable_logPartition
-- name    : BookProof.ChapterLogPartitionConvex.differentiable_logPartition
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-09T12:32:46.62301+00:00
-- url     : https://prove2.me/theorems/0c952577-12d2-4985-b67d-dda475354f77
-- title:
--   `BookProof.ChapterLogPartitionConvex.differentiable_logPartition` (s : Fin m → ℝ) (i : Fin m) : Differentiable ℝ fun b : ℝ => logPartition b s
-- statement:
--   Prove the following Lean 4 theorem from `ChapterLogPartitionConvex`.
--
--   `BookProof.ChapterLogPartitionConvex.differentiable_logPartition` (s : Fin m → ℝ) (i : Fin m) : Differentiable ℝ fun b : ℝ => logPartition b s
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterLogPartitionConvex.differentiable_logPartition`.

-- Generated from ChapterLogPartitionConvex.lean — theorem BookProof.ChapterLogPartitionConvex.differentiable_logPartition
import Definitions.Def_ChapterAttentionEntropy
import Definitions.Def_ChapterSoftmaxSharpness
import Mathlib
import Definitions.Def_ChapterLogPartitionConvex
import Definitions.Def_ChapterSoftmaxFluctuation
open BookProof.ChapterLogPartitionConvex


open scoped BigOperators

noncomputable section


open BookProof.ChapterAttentionEntropy BookProof.ChapterSoftmaxSharpness
open BookProof.ChapterSoftmaxFluctuation

variable {m : ℕ}

theorem BookProof.ChapterLogPartitionConvex.differentiable_logPartition (s : Fin m → ℝ) (i : Fin m) :
    Differentiable ℝ fun b : ℝ => logPartition b s := by sorry
