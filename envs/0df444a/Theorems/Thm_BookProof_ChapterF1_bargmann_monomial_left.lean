-- Prove2me | Theorems.Thm_BookProof_ChapterF1_bargmann_monomial_left
-- name    : BookProof.ChapterF1.bargmann_monomial_left
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-08T03:44:31.719488+00:00
-- url     : https://prove2.me/theorems/9d6b0c13-e864-4cab-972b-4aefe6b2a52f
-- title:
--   `BookProof.ChapterF1.bargmann_monomial_left` (m : ℕ) (q : ℂ[X]) : bargmann (X ^ m) q = (m.factorial : ℂ) * q.coeff m
-- statement:
--   Prove the following Lean 4 theorem from `ChapterF1`.
--
--   `BookProof.ChapterF1.bargmann_monomial_left` (m : ℕ) (q : ℂ[X]) : bargmann (X ^ m) q = (m.factorial : ℂ) * q.coeff m
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterF1.bargmann_monomial_left`.

-- Generated from ChapterF1.lean — theorem BookProof.ChapterF1.bargmann_monomial_left
import Mathlib
import Definitions.Def_ChapterF1
open BookProof.ChapterF1


open Polynomial Finset
open scoped BigOperators


noncomputable section

theorem BookProof.ChapterF1.bargmann_monomial_left (m : ℕ) (q : ℂ[X]) :
    bargmann (X ^ m) q = (m.factorial : ℂ) * q.coeff m := by sorry
