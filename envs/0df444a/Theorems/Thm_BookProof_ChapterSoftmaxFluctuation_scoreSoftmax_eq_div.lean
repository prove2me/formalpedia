-- Prove2me | Theorems.Thm_BookProof_ChapterSoftmaxFluctuation_scoreSoftmax_eq_div
-- name    : BookProof.ChapterSoftmaxFluctuation.scoreSoftmax_eq_div
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T14:15:34.674236+00:00
-- url     : https://prove2.me/theorems/02b6da1b-5f4e-4630-8a9b-446dc693d7c3
-- title:
--   `BookProof.ChapterSoftmaxFluctuation.scoreSoftmax_eq_div` (beta : ℝ) (s : Fin m → ℝ) (j : Fin m) : scoreSoftmax beta s j = Real.exp (beta * s j) / partition beta s
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSoftmaxFluctuation`.
--
--   `BookProof.ChapterSoftmaxFluctuation.scoreSoftmax_eq_div` (beta : ℝ) (s : Fin m → ℝ) (j : Fin m) : scoreSoftmax beta s j = Real.exp (beta * s j) / partition beta s
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSoftmaxFluctuation.scoreSoftmax_eq_div`.

-- Generated from ChapterSoftmaxFluctuation.lean — theorem BookProof.ChapterSoftmaxFluctuation.scoreSoftmax_eq_div
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

theorem BookProof.ChapterSoftmaxFluctuation.scoreSoftmax_eq_div (beta : ℝ) (s : Fin m → ℝ) (j : Fin m) :
    scoreSoftmax beta s j = Real.exp (beta * s j) / partition beta s := by sorry
