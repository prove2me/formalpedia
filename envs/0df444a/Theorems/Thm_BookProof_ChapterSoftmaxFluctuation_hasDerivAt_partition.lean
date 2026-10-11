-- Prove2me | Theorems.Thm_BookProof_ChapterSoftmaxFluctuation_hasDerivAt_partition
-- name    : BookProof.ChapterSoftmaxFluctuation.hasDerivAt_partition
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T14:16:18.451197+00:00
-- url     : https://prove2.me/theorems/30942b55-5a44-49bf-98a6-33a64a1c20f7
-- title:
--   `BookProof.ChapterSoftmaxFluctuation.hasDerivAt_partition` (beta : ℝ) (s : Fin m → ℝ) : HasDerivAt (fun b : ℝ => partition b s) (∑ l, s l * Real.exp (beta * s l)) beta
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSoftmaxFluctuation`.
--
--   `BookProof.ChapterSoftmaxFluctuation.hasDerivAt_partition` (beta : ℝ) (s : Fin m → ℝ) : HasDerivAt (fun b : ℝ => partition b s) (∑ l, s l * Real.exp (beta * s l)) beta
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSoftmaxFluctuation.hasDerivAt_partition`.

-- Generated from ChapterSoftmaxFluctuation.lean — theorem BookProof.ChapterSoftmaxFluctuation.hasDerivAt_partition
import Definitions.Def_ChapterSoftmaxSharpness
import Definitions.Def_ChapterSoftmaxOrder
import Mathlib
import Definitions.Def_ChapterSoftmaxFluctuation
open BookProof.ChapterSoftmaxFluctuation


open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m : ℕ}

theorem BookProof.ChapterSoftmaxFluctuation.hasDerivAt_partition (beta : ℝ) (s : Fin m → ℝ) :
    HasDerivAt (fun b : ℝ => partition b s)
      (∑ l, s l * Real.exp (beta * s l)) beta := by sorry
