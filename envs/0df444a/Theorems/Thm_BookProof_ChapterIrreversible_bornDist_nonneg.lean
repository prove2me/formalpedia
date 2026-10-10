-- Prove2me | Theorems.Thm_BookProof_ChapterIrreversible_bornDist_nonneg
-- name    : BookProof.ChapterIrreversible.bornDist_nonneg
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:18:12.471583+00:00
-- url     : https://prove2.me/theorems/3fb07a36-d3fb-489e-a887-3ac43eecc9f2
-- title:
--   `BookProof.ChapterIrreversible.bornDist_nonneg` (v : Fin n → ℂ) (a : Fin n) : 0 ≤ bornDist v a
-- statement:
--   Prove the following Lean 4 theorem from `ChapterIrreversible`.
--
--   `BookProof.ChapterIrreversible.bornDist_nonneg` (v : Fin n → ℂ) (a : Fin n) : 0 ≤ bornDist v a
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterIrreversible.bornDist_nonneg`.

-- Generated from ChapterIrreversible.lean — theorem BookProof.ChapterIrreversible.bornDist_nonneg
import Mathlib
import Definitions.Def_ChapterIrreversible
open BookProof.ChapterIrreversible


open scoped BigOperators
open Finset


variable {n : ℕ}

theorem BookProof.ChapterIrreversible.bornDist_nonneg (v : Fin n → ℂ) (a : Fin n) : 0 ≤ bornDist v a := by sorry
