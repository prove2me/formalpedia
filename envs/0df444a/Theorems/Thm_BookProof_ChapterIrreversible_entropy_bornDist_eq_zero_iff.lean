-- Prove2me | Theorems.Thm_BookProof_ChapterIrreversible_entropy_bornDist_eq_zero_iff
-- name    : BookProof.ChapterIrreversible.entropy_bornDist_eq_zero_iff
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:18:57.970824+00:00
-- url     : https://prove2.me/theorems/b8250c94-e044-435e-9fc6-a0dd05a88e72
-- title:
--   `BookProof.ChapterIrreversible.entropy_bornDist_eq_zero_iff` (v : Fin n → ℂ) (hv : ∑ a, ‖v a‖ ^ 2 = 1) : entropy (bornDist v) = 0 ↔ IsDeterministicColumn v
-- statement:
--   Prove the following Lean 4 theorem from `ChapterIrreversible`.
--
--   `BookProof.ChapterIrreversible.entropy_bornDist_eq_zero_iff` (v : Fin n → ℂ) (hv : ∑ a, ‖v a‖ ^ 2 = 1) : entropy (bornDist v) = 0 ↔ IsDeterministicColumn v
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterIrreversible.entropy_bornDist_eq_zero_iff`.

-- Generated from ChapterIrreversible.lean — theorem BookProof.ChapterIrreversible.entropy_bornDist_eq_zero_iff
import Mathlib
import Definitions.Def_ChapterIrreversible
open BookProof.ChapterIrreversible


open scoped BigOperators
open Finset


variable {n : ℕ}

theorem BookProof.ChapterIrreversible.entropy_bornDist_eq_zero_iff (v : Fin n → ℂ) (hv : ∑ a, ‖v a‖ ^ 2 = 1) :
    entropy (bornDist v) = 0 ↔ IsDeterministicColumn v := by sorry
