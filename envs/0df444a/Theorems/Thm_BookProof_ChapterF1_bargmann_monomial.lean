-- Prove2me | Theorems.Thm_BookProof_ChapterF1_bargmann_monomial
-- name    : BookProof.ChapterF1.bargmann_monomial
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-08T03:44:52.383465+00:00
-- url     : https://prove2.me/theorems/33aefd5e-4925-4369-84f2-075034f93f6e
-- title:
--   `BookProof.ChapterF1.bargmann_monomial` (m n : ℕ) : bargmann (X ^ m) (X ^ n) = if m = n then (n.factorial : ℂ) else 0
-- statement:
--   Prove the following Lean 4 theorem from `ChapterF1`.
--
--   `BookProof.ChapterF1.bargmann_monomial` (m n : ℕ) : bargmann (X ^ m) (X ^ n) = if m = n then (n.factorial : ℂ) else 0
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterF1.bargmann_monomial`.

-- Generated from ChapterF1.lean — theorem BookProof.ChapterF1.bargmann_monomial
import Mathlib
import Definitions.Def_ChapterF1
open BookProof.ChapterF1


open Polynomial Finset
open scoped BigOperators


noncomputable section

theorem BookProof.ChapterF1.bargmann_monomial (m n : ℕ) :
    bargmann (X ^ m) (X ^ n) = if m = n then (n.factorial : ℂ) else 0 := by sorry
