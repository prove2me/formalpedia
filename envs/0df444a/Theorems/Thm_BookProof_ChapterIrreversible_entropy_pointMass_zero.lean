-- Prove2me | Theorems.Thm_BookProof_ChapterIrreversible_entropy_pointMass_zero
-- name    : BookProof.ChapterIrreversible.entropy_pointMass_zero
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:18:15.880977+00:00
-- url     : https://prove2.me/theorems/b55e7739-0423-4cc4-81cc-edbfed380449
-- title:
--   `BookProof.ChapterIrreversible.entropy_pointMass_zero` (p : Fin n → ℝ) (hp : IsPointMass p) : entropy p = 0
-- statement:
--   Prove the following Lean 4 theorem from `ChapterIrreversible`.
--
--   `BookProof.ChapterIrreversible.entropy_pointMass_zero` (p : Fin n → ℝ) (hp : IsPointMass p) : entropy p = 0
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterIrreversible.entropy_pointMass_zero`.

-- Generated from ChapterIrreversible.lean — theorem BookProof.ChapterIrreversible.entropy_pointMass_zero
import Mathlib
import Definitions.Def_ChapterIrreversible
open BookProof.ChapterIrreversible


open scoped BigOperators
open Finset


variable {n : ℕ}

theorem BookProof.ChapterIrreversible.entropy_pointMass_zero (p : Fin n → ℝ) (hp : IsPointMass p) :
    entropy p = 0 := by sorry
