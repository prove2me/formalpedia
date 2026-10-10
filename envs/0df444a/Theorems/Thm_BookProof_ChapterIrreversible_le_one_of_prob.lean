-- Prove2me | Theorems.Thm_BookProof_ChapterIrreversible_le_one_of_prob
-- name    : BookProof.ChapterIrreversible.le_one_of_prob
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:18:03.420997+00:00
-- url     : https://prove2.me/theorems/52ae8cb6-47b7-416a-aa6e-8f5ca3977379
-- title:
--   `BookProof.ChapterIrreversible.le_one_of_prob` (p : Fin n → ℝ) (hnn : ∀ a, 0 ≤ p a) (hsum : ∑ a, p a = 1) (a : Fin n) : p a ≤ 1
-- statement:
--   Prove the following Lean 4 theorem from `ChapterIrreversible`.
--
--   `BookProof.ChapterIrreversible.le_one_of_prob` (p : Fin n → ℝ) (hnn : ∀ a, 0 ≤ p a) (hsum : ∑ a, p a = 1) (a : Fin n) : p a ≤ 1
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterIrreversible.le_one_of_prob`.

-- Generated from ChapterIrreversible.lean — theorem BookProof.ChapterIrreversible.le_one_of_prob
import Mathlib
import Definitions.Def_ChapterIrreversible
open BookProof.ChapterIrreversible


open scoped BigOperators
open Finset


variable {n : ℕ}

theorem BookProof.ChapterIrreversible.le_one_of_prob (p : Fin n → ℝ) (hnn : ∀ a, 0 ≤ p a)
    (hsum : ∑ a, p a = 1) (a : Fin n) : p a ≤ 1 := by sorry
