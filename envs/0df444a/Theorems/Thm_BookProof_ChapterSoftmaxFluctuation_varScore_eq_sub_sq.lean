-- Prove2me | Theorems.Thm_BookProof_ChapterSoftmaxFluctuation_varScore_eq_sub_sq
-- name    : BookProof.ChapterSoftmaxFluctuation.varScore_eq_sub_sq
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T14:17:16.831212+00:00
-- url     : https://prove2.me/theorems/f563b602-6739-4c31-ba89-5ff11bad8bc3
-- title:
--   `BookProof.ChapterSoftmaxFluctuation.varScore_eq_sub_sq` (beta : ℝ) (s : Fin m → ℝ) (i : Fin m) : varScore beta s = (∑ l, scoreSoftmax beta s l * s l ^ 2) - meanScore beta s ^ 2
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSoftmaxFluctuation`.
--
--   `BookProof.ChapterSoftmaxFluctuation.varScore_eq_sub_sq` (beta : ℝ) (s : Fin m → ℝ) (i : Fin m) : varScore beta s = (∑ l, scoreSoftmax beta s l * s l ^ 2) - meanScore beta s ^ 2
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSoftmaxFluctuation.varScore_eq_sub_sq`.

-- Generated from ChapterSoftmaxFluctuation.lean — theorem BookProof.ChapterSoftmaxFluctuation.varScore_eq_sub_sq
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

theorem BookProof.ChapterSoftmaxFluctuation.varScore_eq_sub_sq (beta : ℝ) (s : Fin m → ℝ) (i : Fin m) :
    varScore beta s = (∑ l, scoreSoftmax beta s l * s l ^ 2) - meanScore beta s ^ 2 := by sorry
