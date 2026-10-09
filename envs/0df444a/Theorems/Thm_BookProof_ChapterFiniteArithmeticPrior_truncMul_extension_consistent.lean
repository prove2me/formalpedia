-- Prove2me | Theorems.Thm_BookProof_ChapterFiniteArithmeticPrior_truncMul_extension_consistent
-- name    : BookProof.ChapterFiniteArithmeticPrior.truncMul_extension_consistent
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-08T10:23:01.540328+00:00
-- url     : https://prove2.me/theorems/0536cbb0-7cd1-446b-9901-df045471feca
-- title:
--   `BookProof.ChapterFiniteArithmeticPrior.truncMul_extension_consistent` {B : ℕ} [NeZero B] {H : Type*} [Fintype H] (E : BayesianArithmeticExtension B H) (hE : E.known = truncMul B)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFiniteArithmeticPrior`.
--
--   `BookProof.ChapterFiniteArithmeticPrior.truncMul_extension_consistent` {B : ℕ} [NeZero B] {H : Type*} [Fintype H] (E : BayesianArithmeticExtension B H) (hE : E.known = truncMul B) (a b : Fin B) (h : (a : ℕ) * (b : ℕ) < B) : ((E.known.result a b : Fin B) : ℕ) = (a : ℕ) * (b : ℕ) ∧ (∀ x, 0 ≤ E.prior x) ∧ ∑ x, E.prior x = 1
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterFiniteArithmeticPrior.truncMul_extension_consistent`.

-- Generated from ChapterFiniteArithmeticPrior.lean — theorem BookProof.ChapterFiniteArithmeticPrior.truncMul_extension_consistent
import Mathlib
import Definitions.Def_ChapterFiniteArithmeticPrior
open BookProof.ChapterFiniteArithmeticPrior

theorem BookProof.ChapterFiniteArithmeticPrior.truncMul_extension_consistent {B : ℕ} [NeZero B] {H : Type*} [Fintype H]
    (E : BayesianArithmeticExtension B H) (hE : E.known = truncMul B)
    (a b : Fin B) (h : (a : ℕ) * (b : ℕ) < B) :
    ((E.known.result a b : Fin B) : ℕ) = (a : ℕ) * (b : ℕ) ∧
      (∀ x, 0 ≤ E.prior x) ∧ ∑ x, E.prior x = 1 := by sorry
