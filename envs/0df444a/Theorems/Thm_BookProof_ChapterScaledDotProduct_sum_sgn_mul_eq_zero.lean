-- Prove2me | Theorems.Thm_BookProof_ChapterScaledDotProduct_sum_sgn_mul_eq_zero
-- name    : BookProof.ChapterScaledDotProduct.sum_sgn_mul_eq_zero
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T11:43:59.667861+00:00
-- url     : https://prove2.me/theorems/07223f99-6e72-4b9b-b188-c21ac4dfe488
-- title:
--   `BookProof.ChapterScaledDotProduct.sum_sgn_mul_eq_zero` {i j : Fin d} (hij : i ≠ j) : ∑ x : (Fin d → Bool), sgn (x i) * sgn (x j) = 0
-- statement:
--   Prove the following Lean 4 theorem from `ChapterScaledDotProduct`.
--
--   `BookProof.ChapterScaledDotProduct.sum_sgn_mul_eq_zero` {i j : Fin d} (hij : i ≠ j) : ∑ x : (Fin d → Bool), sgn (x i) * sgn (x j) = 0
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterScaledDotProduct.sum_sgn_mul_eq_zero`.

-- Generated from ChapterScaledDotProduct.lean — theorem BookProof.ChapterScaledDotProduct.sum_sgn_mul_eq_zero
import Definitions.Def_ChapterSoftmaxSharpness
import Mathlib
import Definitions.Def_ChapterScaledDotProduct
open BookProof.ChapterScaledDotProduct


open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness

variable {d : ℕ}

theorem BookProof.ChapterScaledDotProduct.sum_sgn_mul_eq_zero {i j : Fin d} (hij : i ≠ j) :
    ∑ x : (Fin d → Bool), sgn (x i) * sgn (x j) = 0 := by sorry
