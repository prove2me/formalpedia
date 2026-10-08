-- Prove2me | Theorems.Thm_BookProof_FreeFieldConstraint_constraint_commutation_identity
-- name    : BookProof.FreeFieldConstraint.constraint_commutation_identity
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-05T08:40:49.822029+00:00
-- url     : https://prove2.me/theorems/93f1c563-d035-42e3-96b7-ef751804c39e
-- title:
--   `BookProof.FreeFieldConstraint.constraint_commutation_identity` (D H A : R) (hDH : bracket D H = 0) : bracket (bracket D A) H = - bracket D (bracket H A)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFreeFieldConstraint`.
--
--   `BookProof.FreeFieldConstraint.constraint_commutation_identity` (D H A : R) (hDH : bracket D H = 0) : bracket (bracket D A) H = - bracket D (bracket H A)
--
--   Formalization note: Lean 4 identifier `BookProof.FreeFieldConstraint.constraint_commutation_identity`.

-- Generated from ChapterFreeFieldConstraint.lean — theorem BookProof.FreeFieldConstraint.constraint_commutation_identity
import Mathlib
import Definitions.Def_ChapterFreeFieldConstraint
open BookProof.FreeFieldConstraint

variable {R : Type*} [Ring R]

theorem BookProof.FreeFieldConstraint.constraint_commutation_identity (D H A : R) (hDH : bracket D H = 0) :
    bracket (bracket D A) H = - bracket D (bracket H A) := by sorry
