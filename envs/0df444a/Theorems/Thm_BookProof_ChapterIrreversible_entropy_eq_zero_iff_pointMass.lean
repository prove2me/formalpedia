-- Prove2me | Theorems.Thm_BookProof_ChapterIrreversible_entropy_eq_zero_iff_pointMass
-- name    : BookProof.ChapterIrreversible.entropy_eq_zero_iff_pointMass
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:18:36.686262+00:00
-- url     : https://prove2.me/theorems/5f9e1c5c-dc61-4642-a3b5-2c3269ed1e09
-- title:
--   `BookProof.ChapterIrreversible.entropy_eq_zero_iff_pointMass` (p : Fin n → ℝ) (hnn : ∀ a, 0 ≤ p a) (hsum : ∑ a, p a = 1) : entropy p = 0 ↔ IsPointMass p
-- statement:
--   Prove the following Lean 4 theorem from `ChapterIrreversible`.
--
--   `BookProof.ChapterIrreversible.entropy_eq_zero_iff_pointMass` (p : Fin n → ℝ) (hnn : ∀ a, 0 ≤ p a) (hsum : ∑ a, p a = 1) : entropy p = 0 ↔ IsPointMass p
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterIrreversible.entropy_eq_zero_iff_pointMass`.

-- Generated from ChapterIrreversible.lean — theorem BookProof.ChapterIrreversible.entropy_eq_zero_iff_pointMass
import Mathlib
import Definitions.Def_ChapterIrreversible
open BookProof.ChapterIrreversible


open scoped BigOperators
open Finset


variable {n : ℕ}

theorem BookProof.ChapterIrreversible.entropy_eq_zero_iff_pointMass (p : Fin n → ℝ) (hnn : ∀ a, 0 ≤ p a)
    (hsum : ∑ a, p a = 1) : entropy p = 0 ↔ IsPointMass p := by sorry
