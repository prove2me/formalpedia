-- Prove2me | Theorems.Thm_BookProof_ConservativeDiagonal_eventProj_idem
-- name    : BookProof.ConservativeDiagonal.eventProj_idem
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T22:22:58.835026+00:00
-- url     : https://prove2.me/theorems/e0a9abb4-ddbf-45a6-b01a-dbccc7170d42
-- title:
--   `BookProof.ConservativeDiagonal.eventProj_idem` (S : Finset n) : eventProj S * eventProj S = eventProj S
-- statement:
--   Prove the following Lean 4 theorem from `ChapterConservativeDiagonal`.
--
--   `BookProof.ConservativeDiagonal.eventProj_idem` (S : Finset n) : eventProj S * eventProj S = eventProj S
--
--   Formalization note: Lean 4 identifier `BookProof.ConservativeDiagonal.eventProj_idem`.

-- Generated from ChapterConservativeDiagonal.lean — theorem BookProof.ConservativeDiagonal.eventProj_idem
import Definitions.Def_ChapterFreeFieldConstraint
import Mathlib
import Definitions.Def_ChapterConservativeDiagonal
open BookProof.ConservativeDiagonal


open scoped Matrix
open Matrix BookProof.FreeFieldConstraint


variable {n : Type*} [Fintype n] [DecidableEq n]

theorem BookProof.ConservativeDiagonal.eventProj_idem (S : Finset n) : eventProj S * eventProj S = eventProj S := by sorry
