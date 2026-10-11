-- Prove2me | Theorems.Thm_BookProof_ChapterScaledDotProduct_sum_sgn_mul_self
-- name    : BookProof.ChapterScaledDotProduct.sum_sgn_mul_self
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T11:44:20.586986+00:00
-- url     : https://prove2.me/theorems/acf4c73d-30f6-451a-bda2-61e7990a033b
-- title:
--   `BookProof.ChapterScaledDotProduct.sum_sgn_mul_self` (i : Fin d) : ∑ x : (Fin d → Bool), sgn (x i) * sgn (x i) = 2 ^ d
-- statement:
--   Prove the following Lean 4 theorem from `ChapterScaledDotProduct`.
--
--   `BookProof.ChapterScaledDotProduct.sum_sgn_mul_self` (i : Fin d) : ∑ x : (Fin d → Bool), sgn (x i) * sgn (x i) = 2 ^ d
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterScaledDotProduct.sum_sgn_mul_self`.

-- Generated from ChapterScaledDotProduct.lean — theorem BookProof.ChapterScaledDotProduct.sum_sgn_mul_self
import Definitions.Def_ChapterSoftmaxSharpness
import Mathlib
import Definitions.Def_ChapterScaledDotProduct
open BookProof.ChapterScaledDotProduct


open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness

variable {d : ℕ}

theorem BookProof.ChapterScaledDotProduct.sum_sgn_mul_self (i : Fin d) :
    ∑ x : (Fin d → Bool), sgn (x i) * sgn (x i) = 2 ^ d := by sorry
