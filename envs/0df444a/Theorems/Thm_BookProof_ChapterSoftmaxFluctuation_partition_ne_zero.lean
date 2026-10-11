-- Prove2me | Theorems.Thm_BookProof_ChapterSoftmaxFluctuation_partition_ne_zero
-- name    : BookProof.ChapterSoftmaxFluctuation.partition_ne_zero
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T14:16:47.440047+00:00
-- url     : https://prove2.me/theorems/bda6c4c8-e53f-4617-9d98-ecfe2d238399
-- title:
--   `BookProof.ChapterSoftmaxFluctuation.partition_ne_zero` (beta : ℝ) (s : Fin m → ℝ) (i : Fin m) : partition beta s ≠ 0
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSoftmaxFluctuation`.
--
--   `BookProof.ChapterSoftmaxFluctuation.partition_ne_zero` (beta : ℝ) (s : Fin m → ℝ) (i : Fin m) : partition beta s ≠ 0
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSoftmaxFluctuation.partition_ne_zero`.

-- Generated from ChapterSoftmaxFluctuation.lean — theorem BookProof.ChapterSoftmaxFluctuation.partition_ne_zero
import Definitions.Def_ChapterSoftmaxSharpness
import Definitions.Def_ChapterSoftmaxOrder
import Mathlib
import Definitions.Def_ChapterSoftmaxFluctuation
open BookProof.ChapterSoftmaxFluctuation


open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m : ℕ}

theorem BookProof.ChapterSoftmaxFluctuation.partition_ne_zero (beta : ℝ) (s : Fin m → ℝ) (i : Fin m) : partition beta s ≠ 0 := by sorry
