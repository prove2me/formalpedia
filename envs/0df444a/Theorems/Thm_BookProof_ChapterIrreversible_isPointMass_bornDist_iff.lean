-- Prove2me | Theorems.Thm_BookProof_ChapterIrreversible_isPointMass_bornDist_iff
-- name    : BookProof.ChapterIrreversible.isPointMass_bornDist_iff
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:18:51.348788+00:00
-- url     : https://prove2.me/theorems/6f3ed2f8-1364-4a8e-a45c-936c80f6a187
-- title:
--   `BookProof.ChapterIrreversible.isPointMass_bornDist_iff` (v : Fin n → ℂ) (hv : ∑ a, ‖v a‖ ^ 2 = 1) : IsPointMass (bornDist v) ↔ IsDeterministicColumn v
-- statement:
--   Prove the following Lean 4 theorem from `ChapterIrreversible`.
--
--   `BookProof.ChapterIrreversible.isPointMass_bornDist_iff` (v : Fin n → ℂ) (hv : ∑ a, ‖v a‖ ^ 2 = 1) : IsPointMass (bornDist v) ↔ IsDeterministicColumn v
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterIrreversible.isPointMass_bornDist_iff`.

-- Generated from ChapterIrreversible.lean — theorem BookProof.ChapterIrreversible.isPointMass_bornDist_iff
import Mathlib
import Definitions.Def_ChapterIrreversible
open BookProof.ChapterIrreversible


open scoped BigOperators
open Finset


variable {n : ℕ}

theorem BookProof.ChapterIrreversible.isPointMass_bornDist_iff (v : Fin n → ℂ) (hv : ∑ a, ‖v a‖ ^ 2 = 1) :
    IsPointMass (bornDist v) ↔ IsDeterministicColumn v := by sorry
