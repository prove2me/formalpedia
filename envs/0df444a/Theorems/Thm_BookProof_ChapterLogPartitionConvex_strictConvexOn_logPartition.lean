-- Prove2me | Theorems.Thm_BookProof_ChapterLogPartitionConvex_strictConvexOn_logPartition
-- name    : BookProof.ChapterLogPartitionConvex.strictConvexOn_logPartition
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-09T12:33:39.001704+00:00
-- url     : https://prove2.me/theorems/43be7fab-0d19-4413-a54e-c93e630a023e
-- title:
--   `BookProof.ChapterLogPartitionConvex.strictConvexOn_logPartition` {s : Fin m → ℝ} {a b : Fin m} (hab : s a ≠ s b) : StrictConvexOn ℝ Set.univ fun c : ℝ => logPartition c s
-- statement:
--   Prove the following Lean 4 theorem from `ChapterLogPartitionConvex`.
--
--   `BookProof.ChapterLogPartitionConvex.strictConvexOn_logPartition` {s : Fin m → ℝ} {a b : Fin m} (hab : s a ≠ s b) : StrictConvexOn ℝ Set.univ fun c : ℝ => logPartition c s
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterLogPartitionConvex.strictConvexOn_logPartition`.

-- Generated from ChapterLogPartitionConvex.lean — theorem BookProof.ChapterLogPartitionConvex.strictConvexOn_logPartition
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

theorem BookProof.ChapterLogPartitionConvex.strictConvexOn_logPartition {s : Fin m → ℝ} {a b : Fin m} (hab : s a ≠ s b) :
    StrictConvexOn ℝ Set.univ fun c : ℝ => logPartition c s := by sorry
