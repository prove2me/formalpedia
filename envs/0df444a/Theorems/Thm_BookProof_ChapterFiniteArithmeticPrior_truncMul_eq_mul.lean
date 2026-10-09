-- Prove2me | Theorems.Thm_BookProof_ChapterFiniteArithmeticPrior_truncMul_eq_mul
-- name    : BookProof.ChapterFiniteArithmeticPrior.truncMul_eq_mul
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-08T10:19:16.053963+00:00
-- url     : https://prove2.me/theorems/409092b9-c1c9-4eb4-8143-841c473cb2f8
-- title:
--   `BookProof.ChapterFiniteArithmeticPrior.truncMul_eq_mul` {B : ℕ} [NeZero B] (a b : Fin B) (h : (a : ℕ) * (b : ℕ) < B) : (((truncMul B).result a b : Fin B) : ℕ) = (a : ℕ) * (b : ℕ)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFiniteArithmeticPrior`.
--
--   `BookProof.ChapterFiniteArithmeticPrior.truncMul_eq_mul` {B : ℕ} [NeZero B] (a b : Fin B) (h : (a : ℕ) * (b : ℕ) < B) : (((truncMul B).result a b : Fin B) : ℕ) = (a : ℕ) * (b : ℕ)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterFiniteArithmeticPrior.truncMul_eq_mul`.

-- Generated from ChapterFiniteArithmeticPrior.lean — theorem BookProof.ChapterFiniteArithmeticPrior.truncMul_eq_mul
import Mathlib
import Definitions.Def_ChapterFiniteArithmeticPrior
open BookProof.ChapterFiniteArithmeticPrior

theorem BookProof.ChapterFiniteArithmeticPrior.truncMul_eq_mul {B : ℕ} [NeZero B] (a b : Fin B) (h : (a : ℕ) * (b : ℕ) < B) :
    (((truncMul B).result a b : Fin B) : ℕ) = (a : ℕ) * (b : ℕ) := by sorry
