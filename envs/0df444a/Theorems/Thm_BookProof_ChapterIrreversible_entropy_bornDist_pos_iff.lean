-- Prove2me | Theorems.Thm_BookProof_ChapterIrreversible_entropy_bornDist_pos_iff
-- name    : BookProof.ChapterIrreversible.entropy_bornDist_pos_iff
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:19:09.930757+00:00
-- url     : https://prove2.me/theorems/5b9c92e0-28e1-4749-8851-976e7282c014
-- title:
--   `BookProof.ChapterIrreversible.entropy_bornDist_pos_iff` (v : Fin n → ℂ) (hv : ∑ a, ‖v a‖ ^ 2 = 1) : 0 < entropy (bornDist v) ↔ ¬ IsDeterministicColumn v
-- statement:
--   Prove the following Lean 4 theorem from `ChapterIrreversible`.
--
--   `BookProof.ChapterIrreversible.entropy_bornDist_pos_iff` (v : Fin n → ℂ) (hv : ∑ a, ‖v a‖ ^ 2 = 1) : 0 < entropy (bornDist v) ↔ ¬ IsDeterministicColumn v
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterIrreversible.entropy_bornDist_pos_iff`.

-- Generated from ChapterIrreversible.lean — theorem BookProof.ChapterIrreversible.entropy_bornDist_pos_iff
import Mathlib
import Definitions.Def_ChapterIrreversible
open BookProof.ChapterIrreversible


open scoped BigOperators
open Finset


variable {n : ℕ}

theorem BookProof.ChapterIrreversible.entropy_bornDist_pos_iff (v : Fin n → ℂ) (hv : ∑ a, ‖v a‖ ^ 2 = 1) :
    0 < entropy (bornDist v) ↔ ¬ IsDeterministicColumn v := by sorry
