-- Prove2me | Theorems.Thm_BookProof_ChapterFiniteArithmeticPrior_prior_is_probability
-- name    : BookProof.ChapterFiniteArithmeticPrior.prior_is_probability
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-08T05:09:41.61198+00:00
-- url     : https://prove2.me/theorems/02b0d631-1a93-43f2-99f0-f47e8d9be36e
-- title:
--   `BookProof.ChapterFiniteArithmeticPrior.prior_is_probability` {B : ℕ} {H : Type*} [Fintype H] (E : BayesianArithmeticExtension B H) : (∀ h, 0 ≤ E.prior h) ∧ ∑ h, E.prior h = 1
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFiniteArithmeticPrior`.
--
--   `BookProof.ChapterFiniteArithmeticPrior.prior_is_probability` {B : ℕ} {H : Type*} [Fintype H] (E : BayesianArithmeticExtension B H) : (∀ h, 0 ≤ E.prior h) ∧ ∑ h, E.prior h = 1
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterFiniteArithmeticPrior.prior_is_probability`.

-- Generated from ChapterFiniteArithmeticPrior.lean — theorem BookProof.ChapterFiniteArithmeticPrior.prior_is_probability
import Mathlib
import Definitions.Def_ChapterFiniteArithmeticPrior
open BookProof.ChapterFiniteArithmeticPrior

theorem BookProof.ChapterFiniteArithmeticPrior.prior_is_probability {B : ℕ} {H : Type*} [Fintype H]
    (E : BayesianArithmeticExtension B H) :
    (∀ h, 0 ≤ E.prior h) ∧ ∑ h, E.prior h = 1 := by sorry
