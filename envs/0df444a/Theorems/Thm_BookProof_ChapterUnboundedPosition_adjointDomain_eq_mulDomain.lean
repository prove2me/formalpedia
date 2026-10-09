-- Prove2me | Theorems.Thm_BookProof_ChapterUnboundedPosition_adjointDomain_eq_mulDomain
-- name    : BookProof.ChapterUnboundedPosition.adjointDomain_eq_mulDomain
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-09T05:07:39.311081+00:00
-- url     : https://prove2.me/theorems/5772edb8-926d-45cf-91ff-62dc5cbdf97b
-- title:
--   The Lean 4 theorem `adjointDomain_eq_mulDomain` in the `ChapterUnboundedPosition` chapter of the timepiece formalization
-- statement:
--   Formal statement of `BookProof.ChapterUnboundedPosition.adjointDomain_eq_mulDomain` from the timepiece Lean 4 formalization.
-- source:
--   https://github.com/leonardopedro/timepiece

-- Generated from ChapterUnboundedPosition.lean — theorem BookProof.ChapterUnboundedPosition.adjointDomain_eq_mulDomain
import Mathlib
import Definitions.Def_ChapterUnboundedPosition
import Definitions.Def_ChapterContinuityUnitaryInfinite
import Definitions.Def_ChapterF7
open BookProof.ChapterContinuityUnitaryInfinite
open BookProof.ChapterF7
open BookProof.ChapterUnboundedPosition


open scoped ENNReal InnerProductSpace


open BookProof.ChapterContinuityUnitaryInfinite (L2Z)

theorem BookProof.ChapterUnboundedPosition.adjointDomain_eq_mulDomain (f : ℤ → ℝ) :
    adjointDomain f = ((mulDomain f : Submodule ℂ L2Z) : Set L2Z) := by sorry
