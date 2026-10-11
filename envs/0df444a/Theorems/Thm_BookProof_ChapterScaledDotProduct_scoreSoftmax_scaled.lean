-- Prove2me | Theorems.Thm_BookProof_ChapterScaledDotProduct_scoreSoftmax_scaled
-- name    : BookProof.ChapterScaledDotProduct.scoreSoftmax_scaled
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T11:44:47.184264+00:00
-- url     : https://prove2.me/theorems/24107269-ad2a-4437-a467-6e29c999231e
-- title:
--   `BookProof.ChapterScaledDotProduct.scoreSoftmax_scaled` (beta : ℝ) (s : Fin m → ℝ) (j : Fin m) : scoreSoftmax beta (fun l => s l / Real.sqrt d) j = scoreSoftmax (beta / Real.sqrt d
-- statement:
--   Prove the following Lean 4 theorem from `ChapterScaledDotProduct`.
--
--   `BookProof.ChapterScaledDotProduct.scoreSoftmax_scaled` (beta : ℝ) (s : Fin m → ℝ) (j : Fin m) : scoreSoftmax beta (fun l => s l / Real.sqrt d) j = scoreSoftmax (beta / Real.sqrt d) s j
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterScaledDotProduct.scoreSoftmax_scaled`.

-- Generated from ChapterScaledDotProduct.lean — theorem BookProof.ChapterScaledDotProduct.scoreSoftmax_scaled
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

theorem BookProof.ChapterScaledDotProduct.scoreSoftmax_scaled (beta : ℝ) (s : Fin m → ℝ) (j : Fin m) :
    scoreSoftmax beta (fun l => s l / Real.sqrt d) j
      = scoreSoftmax (beta / Real.sqrt d) s j := by sorry
