-- Prove2me | Theorems.Thm_BookProof_ChapterIrreversible_bornDist_sum
-- name    : BookProof.ChapterIrreversible.bornDist_sum
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:17:53.81252+00:00
-- url     : https://prove2.me/theorems/553079b8-5e66-4c74-989e-00df664b3698
-- title:
--   `BookProof.ChapterIrreversible.bornDist_sum` (v : Fin n → ℂ) (hv : ∑ a, ‖v a‖ ^ 2 = 1) : ∑ a, bornDist v a = 1
-- statement:
--   Prove the following Lean 4 theorem from `ChapterIrreversible`.
--
--   `BookProof.ChapterIrreversible.bornDist_sum` (v : Fin n → ℂ) (hv : ∑ a, ‖v a‖ ^ 2 = 1) : ∑ a, bornDist v a = 1
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterIrreversible.bornDist_sum`.

-- Generated from ChapterIrreversible.lean — theorem BookProof.ChapterIrreversible.bornDist_sum
import Mathlib
import Definitions.Def_ChapterIrreversible
open BookProof.ChapterIrreversible


open scoped BigOperators
open Finset


variable {n : ℕ}

theorem BookProof.ChapterIrreversible.bornDist_sum (v : Fin n → ℂ) (hv : ∑ a, ‖v a‖ ^ 2 = 1) :
    ∑ a, bornDist v a = 1 := by sorry
