-- Prove2me | Theorems.Thm_BookProof_ChapterIrreversible_entropy_nonneg
-- name    : BookProof.ChapterIrreversible.entropy_nonneg
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:18:40.592853+00:00
-- url     : https://prove2.me/theorems/8f4a9831-e610-46e7-ad59-7158d5911e71
-- title:
--   `BookProof.ChapterIrreversible.entropy_nonneg` (p : Fin n → ℝ) (hnn : ∀ a, 0 ≤ p a) (hsum : ∑ a, p a = 1) : 0 ≤ entropy p
-- statement:
--   Prove the following Lean 4 theorem from `ChapterIrreversible`.
--
--   `BookProof.ChapterIrreversible.entropy_nonneg` (p : Fin n → ℝ) (hnn : ∀ a, 0 ≤ p a) (hsum : ∑ a, p a = 1) : 0 ≤ entropy p
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterIrreversible.entropy_nonneg`.

-- Generated from ChapterIrreversible.lean — theorem BookProof.ChapterIrreversible.entropy_nonneg
import Mathlib
import Definitions.Def_ChapterIrreversible
open BookProof.ChapterIrreversible


open scoped BigOperators
open Finset


variable {n : ℕ}

theorem BookProof.ChapterIrreversible.entropy_nonneg (p : Fin n → ℝ) (hnn : ∀ a, 0 ≤ p a)
    (hsum : ∑ a, p a = 1) : 0 ≤ entropy p := by sorry
