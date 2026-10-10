-- Prove2me | Theorems.Thm_BookProof_ChapterLogPartitionConvex_convexOn_logPartition
-- name    : BookProof.ChapterLogPartitionConvex.convexOn_logPartition
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-09T12:33:34.415204+00:00
-- url     : https://prove2.me/theorems/61bbba1d-27d0-48e1-8d6c-2fc18ab3b19f
-- title:
--   `BookProof.ChapterLogPartitionConvex.convexOn_logPartition` (s : Fin m → ℝ) (i : Fin m) : ConvexOn ℝ Set.univ fun b : ℝ => logPartition b s
-- statement:
--   Prove the following Lean 4 theorem from `ChapterLogPartitionConvex`.
--
--   `BookProof.ChapterLogPartitionConvex.convexOn_logPartition` (s : Fin m → ℝ) (i : Fin m) : ConvexOn ℝ Set.univ fun b : ℝ => logPartition b s
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterLogPartitionConvex.convexOn_logPartition`.

-- Generated from ChapterLogPartitionConvex.lean — theorem BookProof.ChapterLogPartitionConvex.convexOn_logPartition
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

theorem BookProof.ChapterLogPartitionConvex.convexOn_logPartition (s : Fin m → ℝ) (i : Fin m) :
    ConvexOn ℝ Set.univ fun b : ℝ => logPartition b s := by sorry
