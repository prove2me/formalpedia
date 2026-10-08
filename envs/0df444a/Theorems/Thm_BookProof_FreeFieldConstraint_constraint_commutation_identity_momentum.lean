-- Prove2me | Theorems.Thm_BookProof_FreeFieldConstraint_constraint_commutation_identity_momentum
-- name    : BookProof.FreeFieldConstraint.constraint_commutation_identity_momentum
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-05T08:44:47.048776+00:00
-- url     : https://prove2.me/theorems/a23438d5-5532-4a51-b151-b049d6a99f32
-- title:
--   `BookProof.FreeFieldConstraint.constraint_commutation_identity_momentum` (D H p1 : R) (hDH : bracket D H = 0) : bracket (bracket D p1) H = - bracket D (bracket H p1)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFreeFieldConstraint`.
--
--   `BookProof.FreeFieldConstraint.constraint_commutation_identity_momentum` (D H p1 : R) (hDH : bracket D H = 0) : bracket (bracket D p1) H = - bracket D (bracket H p1)
--
--   Formalization note: Lean 4 identifier `BookProof.FreeFieldConstraint.constraint_commutation_identity_momentum`.

-- Generated from ChapterFreeFieldConstraint.lean — theorem BookProof.FreeFieldConstraint.constraint_commutation_identity_momentum
import Mathlib
import Definitions.Def_ChapterFreeFieldConstraint
open BookProof.FreeFieldConstraint

variable {R : Type*} [Ring R]

theorem BookProof.FreeFieldConstraint.constraint_commutation_identity_momentum (D H p1 : R) (hDH : bracket D H = 0) :
    bracket (bracket D p1) H = - bracket D (bracket H p1) := by sorry
