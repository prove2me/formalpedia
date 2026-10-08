-- Prove2me | Theorems.Thm_BookProof_ConservativeDiagonal_bracket_eventProj_apply
-- name    : BookProof.ConservativeDiagonal.bracket_eventProj_apply
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T22:23:14.103253+00:00
-- url     : https://prove2.me/theorems/85825a9c-2f52-4fe6-ba88-89a9127f9887
-- title:
--   `BookProof.ConservativeDiagonal.bracket_eventProj_apply` (H : Matrix n n ℂ) (S : Finset n) (k l : n) : bracket H (eventProj S) k l = H k l * ((if l ∈ S then (1 : ℂ) else 0) - (if k
-- statement:
--   Prove the following Lean 4 theorem from `ChapterConservativeDiagonal`.
--
--   `BookProof.ConservativeDiagonal.bracket_eventProj_apply` (H : Matrix n n ℂ) (S : Finset n) (k l : n) : bracket H (eventProj S) k l = H k l * ((if l ∈ S then (1 : ℂ) else 0) - (if k ∈ S then (1 : ℂ) else 0))
--
--   Formalization note: Lean 4 identifier `BookProof.ConservativeDiagonal.bracket_eventProj_apply`.

-- Generated from ChapterConservativeDiagonal.lean — theorem BookProof.ConservativeDiagonal.bracket_eventProj_apply
import Mathlib
import Definitions.Def_ChapterConservativeDiagonal
import Definitions.Def_ChapterFreeFieldConstraint
open BookProof.FreeFieldConstraint
open BookProof.ConservativeDiagonal


open scoped Matrix
open Matrix BookProof.FreeFieldConstraint


variable {n : Type*} [Fintype n] [DecidableEq n]

theorem BookProof.ConservativeDiagonal.bracket_eventProj_apply (H : Matrix n n ℂ) (S : Finset n) (k l : n) :
    bracket H (eventProj S) k l
      = H k l * ((if l ∈ S then (1 : ℂ) else 0) - (if k ∈ S then (1 : ℂ) else 0)) := by sorry
