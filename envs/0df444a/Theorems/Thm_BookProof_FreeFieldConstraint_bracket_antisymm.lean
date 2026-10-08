-- Prove2me | Theorems.Thm_BookProof_FreeFieldConstraint_bracket_antisymm
-- name    : BookProof.FreeFieldConstraint.bracket_antisymm
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-05T08:27:22.755758+00:00
-- url     : https://prove2.me/theorems/23e07f38-0ed8-4999-8560-e2887743d850
-- title:
--   `BookProof.FreeFieldConstraint.bracket_antisymm` (a b : R) : bracket a b = - bracket b a
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFreeFieldConstraint`.
--
--   `BookProof.FreeFieldConstraint.bracket_antisymm` (a b : R) : bracket a b = - bracket b a
--
--   Formalization note: Lean 4 identifier `BookProof.FreeFieldConstraint.bracket_antisymm`.

-- Generated from ChapterFreeFieldConstraint.lean — theorem BookProof.FreeFieldConstraint.bracket_antisymm
import Mathlib
import Definitions.Def_ChapterFreeFieldConstraint
open BookProof.FreeFieldConstraint

variable {R : Type*} [Ring R]

theorem BookProof.FreeFieldConstraint.bracket_antisymm (a b : R) : bracket a b = - bracket b a := by sorry
