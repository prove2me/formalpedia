-- Prove2me | Theorems.Thm_BookProof_ChapterSoftmaxFluctuation_varScore_eq_zero_of_const
-- name    : BookProof.ChapterSoftmaxFluctuation.varScore_eq_zero_of_const
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T14:17:37.585991+00:00
-- url     : https://prove2.me/theorems/deb7186a-0ebf-44fc-9e85-f7d60fde7f08
-- title:
--   `BookProof.ChapterSoftmaxFluctuation.varScore_eq_zero_of_const` {s : Fin m → ℝ} {c : ℝ} (hs : ∀ l, s l = c) (beta : ℝ) (i : Fin m) : varScore beta s = 0
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSoftmaxFluctuation`.
--
--   `BookProof.ChapterSoftmaxFluctuation.varScore_eq_zero_of_const` {s : Fin m → ℝ} {c : ℝ} (hs : ∀ l, s l = c) (beta : ℝ) (i : Fin m) : varScore beta s = 0
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSoftmaxFluctuation.varScore_eq_zero_of_const`.

-- Generated from ChapterSoftmaxFluctuation.lean — theorem BookProof.ChapterSoftmaxFluctuation.varScore_eq_zero_of_const
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

theorem BookProof.ChapterSoftmaxFluctuation.varScore_eq_zero_of_const {s : Fin m → ℝ} {c : ℝ} (hs : ∀ l, s l = c)
    (beta : ℝ) (i : Fin m) : varScore beta s = 0 := by sorry
