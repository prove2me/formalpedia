-- Prove2me | Theorems.Thm_BookProof_ConservativeDiagonal_commutes_all_events_iff_isDiag
-- name    : BookProof.ConservativeDiagonal.commutes_all_events_iff_isDiag
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T22:23:45.879981+00:00
-- url     : https://prove2.me/theorems/a6a319c2-9e20-4fb2-b782-aaa55e51637b
-- title:
--   `BookProof.ConservativeDiagonal.commutes_all_events_iff_isDiag` (H : Matrix n n ℂ) : (∀ S : Finset n, bracket H (eventProj S) = 0) ↔ H.IsDiag
-- statement:
--   Prove the following Lean 4 theorem from `ChapterConservativeDiagonal`.
--
--   `BookProof.ConservativeDiagonal.commutes_all_events_iff_isDiag` (H : Matrix n n ℂ) : (∀ S : Finset n, bracket H (eventProj S) = 0) ↔ H.IsDiag
--
--   Formalization note: Lean 4 identifier `BookProof.ConservativeDiagonal.commutes_all_events_iff_isDiag`.

-- Generated from ChapterConservativeDiagonal.lean — theorem BookProof.ConservativeDiagonal.commutes_all_events_iff_isDiag
import Mathlib
import Definitions.Def_ChapterConservativeDiagonal
import Definitions.Def_ChapterFreeFieldConstraint
open BookProof.FreeFieldConstraint
open BookProof.ConservativeDiagonal


open scoped Matrix
open Matrix BookProof.FreeFieldConstraint


variable {n : Type*} [Fintype n] [DecidableEq n]

theorem BookProof.ConservativeDiagonal.commutes_all_events_iff_isDiag (H : Matrix n n ℂ) :
    (∀ S : Finset n, bracket H (eventProj S) = 0) ↔ H.IsDiag := by sorry
