-- Prove2me | Theorems.Thm_BookProof_ConservativeDiagonal_eventProj_commute
-- name    : BookProof.ConservativeDiagonal.eventProj_commute
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T22:23:01.933988+00:00
-- url     : https://prove2.me/theorems/399e2416-6613-42ff-a4ce-108ed4c2b2a2
-- title:
--   `BookProof.ConservativeDiagonal.eventProj_commute` (S T : Finset n) : eventProj S * eventProj T = eventProj T * eventProj S
-- statement:
--   Prove the following Lean 4 theorem from `ChapterConservativeDiagonal`.
--
--   `BookProof.ConservativeDiagonal.eventProj_commute` (S T : Finset n) : eventProj S * eventProj T = eventProj T * eventProj S
--
--   Formalization note: Lean 4 identifier `BookProof.ConservativeDiagonal.eventProj_commute`.

-- Generated from ChapterConservativeDiagonal.lean — theorem BookProof.ConservativeDiagonal.eventProj_commute
import Definitions.Def_ChapterFreeFieldConstraint
import Mathlib
import Definitions.Def_ChapterConservativeDiagonal
open BookProof.ConservativeDiagonal


open scoped Matrix
open Matrix BookProof.FreeFieldConstraint


variable {n : Type*} [Fintype n] [DecidableEq n]

theorem BookProof.ConservativeDiagonal.eventProj_commute (S T : Finset n) :
    eventProj S * eventProj T = eventProj T * eventProj S := by sorry
