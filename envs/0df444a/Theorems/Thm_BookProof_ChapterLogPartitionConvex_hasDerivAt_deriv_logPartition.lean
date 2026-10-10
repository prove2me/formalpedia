-- Prove2me | Theorems.Thm_BookProof_ChapterLogPartitionConvex_hasDerivAt_deriv_logPartition
-- name    : BookProof.ChapterLogPartitionConvex.hasDerivAt_deriv_logPartition
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-09T12:32:54.636404+00:00
-- url     : https://prove2.me/theorems/6dfb3acd-ccfb-43c5-8fc3-49898051f236
-- title:
--   `BookProof.ChapterLogPartitionConvex.hasDerivAt_deriv_logPartition` (beta : ℝ) (s : Fin m → ℝ) (i : Fin m) : HasDerivAt (deriv fun b : ℝ => logPartition b s) (varScore beta s) beta
-- statement:
--   Prove the following Lean 4 theorem from `ChapterLogPartitionConvex`.
--
--   `BookProof.ChapterLogPartitionConvex.hasDerivAt_deriv_logPartition` (beta : ℝ) (s : Fin m → ℝ) (i : Fin m) : HasDerivAt (deriv fun b : ℝ => logPartition b s) (varScore beta s) beta
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterLogPartitionConvex.hasDerivAt_deriv_logPartition`.

-- Generated from ChapterLogPartitionConvex.lean — theorem BookProof.ChapterLogPartitionConvex.hasDerivAt_deriv_logPartition
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

theorem BookProof.ChapterLogPartitionConvex.hasDerivAt_deriv_logPartition (beta : ℝ) (s : Fin m → ℝ) (i : Fin m) :
    HasDerivAt (deriv fun b : ℝ => logPartition b s) (varScore beta s) beta := by sorry
