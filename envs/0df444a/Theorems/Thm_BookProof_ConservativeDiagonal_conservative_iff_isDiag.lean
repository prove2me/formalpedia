-- Prove2me | Theorems.Thm_BookProof_ConservativeDiagonal_conservative_iff_isDiag
-- name    : BookProof.ConservativeDiagonal.conservative_iff_isDiag
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T22:23:40.671977+00:00
-- url     : https://prove2.me/theorems/0d3427fc-a1e1-433a-9c5a-3fd7b857e457
-- title:
--   `BookProof.ConservativeDiagonal.conservative_iff_isDiag` (H : Matrix n n ℂ) : (∀ S T : Finset n, bracket (bracket H (eventProj S)) (eventProj T) = 0) ↔ H.IsDiag
-- statement:
--   Prove the following Lean 4 theorem from `ChapterConservativeDiagonal`.
--
--   `BookProof.ConservativeDiagonal.conservative_iff_isDiag` (H : Matrix n n ℂ) : (∀ S T : Finset n, bracket (bracket H (eventProj S)) (eventProj T) = 0) ↔ H.IsDiag
--
--   Formalization note: Lean 4 identifier `BookProof.ConservativeDiagonal.conservative_iff_isDiag`.

-- Generated from ChapterConservativeDiagonal.lean — theorem BookProof.ConservativeDiagonal.conservative_iff_isDiag
import Mathlib
import Definitions.Def_ChapterConservativeDiagonal
import Definitions.Def_ChapterFreeFieldConstraint
open BookProof.FreeFieldConstraint
open BookProof.ConservativeDiagonal


open scoped Matrix
open Matrix BookProof.FreeFieldConstraint


variable {n : Type*} [Fintype n] [DecidableEq n]

theorem BookProof.ConservativeDiagonal.conservative_iff_isDiag (H : Matrix n n ℂ) :
    (∀ S T : Finset n, bracket (bracket H (eventProj S)) (eventProj T) = 0) ↔ H.IsDiag := by sorry
