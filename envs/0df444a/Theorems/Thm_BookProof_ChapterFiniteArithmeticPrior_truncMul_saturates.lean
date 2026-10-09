-- Prove2me | Theorems.Thm_BookProof_ChapterFiniteArithmeticPrior_truncMul_saturates
-- name    : BookProof.ChapterFiniteArithmeticPrior.truncMul_saturates
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-08T10:19:16.997125+00:00
-- url     : https://prove2.me/theorems/baa0b157-c8d0-4427-aa7c-8e5fe62e839a
-- title:
--   `BookProof.ChapterFiniteArithmeticPrior.truncMul_saturates` {B : ℕ} [NeZero B] (a b : Fin B) (h : ¬ (a : ℕ) * (b : ℕ) < B) : (((truncMul B).result a b : Fin B) : ℕ) = B - 1
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFiniteArithmeticPrior`.
--
--   `BookProof.ChapterFiniteArithmeticPrior.truncMul_saturates` {B : ℕ} [NeZero B] (a b : Fin B) (h : ¬ (a : ℕ) * (b : ℕ) < B) : (((truncMul B).result a b : Fin B) : ℕ) = B - 1
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterFiniteArithmeticPrior.truncMul_saturates`.

-- Generated from ChapterFiniteArithmeticPrior.lean — theorem BookProof.ChapterFiniteArithmeticPrior.truncMul_saturates
import Mathlib
import Definitions.Def_ChapterFiniteArithmeticPrior
open BookProof.ChapterFiniteArithmeticPrior

theorem BookProof.ChapterFiniteArithmeticPrior.truncMul_saturates {B : ℕ} [NeZero B] (a b : Fin B)
    (h : ¬ (a : ℕ) * (b : ℕ) < B) :
    (((truncMul B).result a b : Fin B) : ℕ) = B - 1 := by sorry
