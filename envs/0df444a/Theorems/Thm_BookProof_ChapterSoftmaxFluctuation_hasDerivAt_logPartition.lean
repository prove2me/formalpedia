-- Prove2me | Theorems.Thm_BookProof_ChapterSoftmaxFluctuation_hasDerivAt_logPartition
-- name    : BookProof.ChapterSoftmaxFluctuation.hasDerivAt_logPartition
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T14:16:47.989582+00:00
-- url     : https://prove2.me/theorems/6e1daa81-a6fb-47da-a64c-f7d0ae3f1575
-- title:
--   `BookProof.ChapterSoftmaxFluctuation.hasDerivAt_logPartition` (beta : ℝ) (s : Fin m → ℝ) (i : Fin m) : HasDerivAt (fun b : ℝ => logPartition b s) (meanScore beta s) beta
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSoftmaxFluctuation`.
--
--   `BookProof.ChapterSoftmaxFluctuation.hasDerivAt_logPartition` (beta : ℝ) (s : Fin m → ℝ) (i : Fin m) : HasDerivAt (fun b : ℝ => logPartition b s) (meanScore beta s) beta
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSoftmaxFluctuation.hasDerivAt_logPartition`.

-- Generated from ChapterSoftmaxFluctuation.lean — theorem BookProof.ChapterSoftmaxFluctuation.hasDerivAt_logPartition
import Definitions.Def_ChapterSoftmaxOrder
import Mathlib
import Definitions.Def_ChapterSoftmaxFluctuation
import Definitions.Def_ChapterSoftmaxSharpness
open BookProof.ChapterSoftmaxSharpness
open BookProof.ChapterSoftmaxFluctuation


open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m : ℕ}

theorem BookProof.ChapterSoftmaxFluctuation.hasDerivAt_logPartition (beta : ℝ) (s : Fin m → ℝ) (i : Fin m) :
    HasDerivAt (fun b : ℝ => logPartition b s) (meanScore beta s) beta := by sorry
