-- Prove2me | Theorems.Thm_BookProof_ChapterScaledDotProduct_scoreSoftmax_div
-- name    : BookProof.ChapterScaledDotProduct.scoreSoftmax_div
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T11:44:38.346737+00:00
-- url     : https://prove2.me/theorems/b4159733-630c-4582-9a6d-ab4a985762dc
-- title:
--   `BookProof.ChapterScaledDotProduct.scoreSoftmax_div` (beta c : ℝ) (s : Fin m → ℝ) (j : Fin m) : scoreSoftmax beta (fun l => s l / c) j = scoreSoftmax (beta / c) s j
-- statement:
--   Prove the following Lean 4 theorem from `ChapterScaledDotProduct`.
--
--   `BookProof.ChapterScaledDotProduct.scoreSoftmax_div` (beta c : ℝ) (s : Fin m → ℝ) (j : Fin m) : scoreSoftmax beta (fun l => s l / c) j = scoreSoftmax (beta / c) s j
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterScaledDotProduct.scoreSoftmax_div`.

-- Generated from ChapterScaledDotProduct.lean — theorem BookProof.ChapterScaledDotProduct.scoreSoftmax_div
import Mathlib
import Definitions.Def_ChapterScaledDotProduct
import Definitions.Def_ChapterSoftmaxSharpness
open BookProof.ChapterSoftmaxSharpness
open BookProof.ChapterScaledDotProduct


open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness

variable {d : ℕ}

variable {m : ℕ}

theorem BookProof.ChapterScaledDotProduct.scoreSoftmax_div (beta c : ℝ) (s : Fin m → ℝ) (j : Fin m) :
    scoreSoftmax beta (fun l => s l / c) j = scoreSoftmax (beta / c) s j := by sorry
