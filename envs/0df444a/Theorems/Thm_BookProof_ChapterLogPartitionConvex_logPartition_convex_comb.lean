-- Prove2me | Theorems.Thm_BookProof_ChapterLogPartitionConvex_logPartition_convex_comb
-- name    : BookProof.ChapterLogPartitionConvex.logPartition_convex_comb
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-09T12:33:27.410274+00:00
-- url     : https://prove2.me/theorems/b56a9db3-65ed-4a44-b92a-35827a1550e6
-- title:
--   `BookProof.ChapterLogPartitionConvex.logPartition_convex_comb` (s : Fin m → ℝ) (i : Fin m) (b c t u : ℝ) (ht : 0 ≤ t) (hu : 0 ≤ u) (htu : t + u = 1) : logPartition (t * b + u * c)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterLogPartitionConvex`.
--
--   `BookProof.ChapterLogPartitionConvex.logPartition_convex_comb` (s : Fin m → ℝ) (i : Fin m) (b c t u : ℝ) (ht : 0 ≤ t) (hu : 0 ≤ u) (htu : t + u = 1) : logPartition (t * b + u * c) s ≤ t * logPartition b s + u * logPartition c s
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterLogPartitionConvex.logPartition_convex_comb`.

-- Generated from ChapterLogPartitionConvex.lean — theorem BookProof.ChapterLogPartitionConvex.logPartition_convex_comb
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

theorem BookProof.ChapterLogPartitionConvex.logPartition_convex_comb (s : Fin m → ℝ) (i : Fin m) (b c t u : ℝ)
    (ht : 0 ≤ t) (hu : 0 ≤ u) (htu : t + u = 1) :
    logPartition (t * b + u * c) s ≤ t * logPartition b s + u * logPartition c s := by sorry
