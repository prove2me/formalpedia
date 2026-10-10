-- Prove2me | Theorems.Thm_BookProof_ConservativeDiagonal_eventProj_isDiag
-- name    : BookProof.ConservativeDiagonal.eventProj_isDiag
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T22:22:35.836836+00:00
-- url     : https://prove2.me/theorems/8f1071c0-21ab-4865-9db4-78b4d588a2ef
-- title:
--   `BookProof.ConservativeDiagonal.eventProj_isDiag` (S : Finset n) : (eventProj S).IsDiag
-- statement:
--   Prove the following Lean 4 theorem from `ChapterConservativeDiagonal`.
--
--   `BookProof.ConservativeDiagonal.eventProj_isDiag` (S : Finset n) : (eventProj S).IsDiag
--
--   Formalization note: Lean 4 identifier `BookProof.ConservativeDiagonal.eventProj_isDiag`.

-- Generated from ChapterConservativeDiagonal.lean — theorem BookProof.ConservativeDiagonal.eventProj_isDiag
import Definitions.Def_ChapterFreeFieldConstraint
import Mathlib
import Definitions.Def_ChapterConservativeDiagonal
open BookProof.ConservativeDiagonal


open scoped Matrix
open Matrix BookProof.FreeFieldConstraint


variable {n : Type*} [Fintype n] [DecidableEq n]

theorem BookProof.ConservativeDiagonal.eventProj_isDiag (S : Finset n) : (eventProj S).IsDiag := by sorry
