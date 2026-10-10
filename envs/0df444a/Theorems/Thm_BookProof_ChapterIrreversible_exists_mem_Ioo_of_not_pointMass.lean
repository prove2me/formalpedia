-- Prove2me | Theorems.Thm_BookProof_ChapterIrreversible_exists_mem_Ioo_of_not_pointMass
-- name    : BookProof.ChapterIrreversible.exists_mem_Ioo_of_not_pointMass
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:18:24.948837+00:00
-- url     : https://prove2.me/theorems/6fc996c5-e435-4936-927c-81a27bb6cfe3
-- title:
--   `BookProof.ChapterIrreversible.exists_mem_Ioo_of_not_pointMass` (p : Fin n → ℝ) (hnn : ∀ a, 0 ≤ p a) (hsum : ∑ a, p a = 1) (hnp : ¬ IsPointMass p) : ∃ a, 0 < p a ∧ p a < 1
-- statement:
--   Prove the following Lean 4 theorem from `ChapterIrreversible`.
--
--   `BookProof.ChapterIrreversible.exists_mem_Ioo_of_not_pointMass` (p : Fin n → ℝ) (hnn : ∀ a, 0 ≤ p a) (hsum : ∑ a, p a = 1) (hnp : ¬ IsPointMass p) : ∃ a, 0 < p a ∧ p a < 1
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterIrreversible.exists_mem_Ioo_of_not_pointMass`.

-- Generated from ChapterIrreversible.lean — theorem BookProof.ChapterIrreversible.exists_mem_Ioo_of_not_pointMass
import Mathlib
import Definitions.Def_ChapterIrreversible
open BookProof.ChapterIrreversible


open scoped BigOperators
open Finset


variable {n : ℕ}

theorem BookProof.ChapterIrreversible.exists_mem_Ioo_of_not_pointMass (p : Fin n → ℝ) (hnn : ∀ a, 0 ≤ p a)
    (hsum : ∑ a, p a = 1) (hnp : ¬ IsPointMass p) :
    ∃ a, 0 < p a ∧ p a < 1 := by sorry
