-- Prove2me | Theorems.Thm_BookProof_ChapterIrreversible_entropy_pos_of_not_pointMass
-- name    : BookProof.ChapterIrreversible.entropy_pos_of_not_pointMass
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:18:40.045565+00:00
-- url     : https://prove2.me/theorems/bcf8acae-c78a-41a2-8fcd-1ead23eb0c14
-- title:
--   `BookProof.ChapterIrreversible.entropy_pos_of_not_pointMass` (p : Fin n → ℝ) (hnn : ∀ a, 0 ≤ p a) (hsum : ∑ a, p a = 1) (hnp : ¬ IsPointMass p) : 0 < entropy p
-- statement:
--   Prove the following Lean 4 theorem from `ChapterIrreversible`.
--
--   `BookProof.ChapterIrreversible.entropy_pos_of_not_pointMass` (p : Fin n → ℝ) (hnn : ∀ a, 0 ≤ p a) (hsum : ∑ a, p a = 1) (hnp : ¬ IsPointMass p) : 0 < entropy p
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterIrreversible.entropy_pos_of_not_pointMass`.

-- Generated from ChapterIrreversible.lean — theorem BookProof.ChapterIrreversible.entropy_pos_of_not_pointMass
import Mathlib
import Definitions.Def_ChapterIrreversible
open BookProof.ChapterIrreversible


open scoped BigOperators
open Finset


variable {n : ℕ}

theorem BookProof.ChapterIrreversible.entropy_pos_of_not_pointMass (p : Fin n → ℝ) (hnn : ∀ a, 0 ≤ p a)
    (hsum : ∑ a, p a = 1) (hnp : ¬ IsPointMass p) : 0 < entropy p := by sorry
