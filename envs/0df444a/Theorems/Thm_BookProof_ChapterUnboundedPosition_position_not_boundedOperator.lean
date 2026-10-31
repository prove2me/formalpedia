-- Prove2me | Theorems.Thm_BookProof_ChapterUnboundedPosition_position_not_boundedOperator
-- name    : BookProof.ChapterUnboundedPosition.position_not_boundedOperator
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-30T22:46:09.931577+00:00
-- url     : https://prove2.me/theorems/c1bd6617-e8e3-4d3a-9dda-233f2deb85f2
-- title:
--   The Lean 4 theorem `position_not_boundedOperator` in the `ChapterUnboundedPosition` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `position_not_boundedOperator` in the `ChapterUnboundedPosition` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterUnboundedPosition.lean

-- Generated from ChapterUnboundedPosition.lean — theorem BookProof.ChapterUnboundedPosition.position_not_boundedOperator
import Mathlib
import Definitions.Def_ChapterUnboundedPosition
import Definitions.Def_ChapterContinuityUnitaryInfinite
import Definitions.Def_ChapterF7
import Definitions.Def_ChapterF7
open BookProof.ChapterContinuityUnitaryInfinite
open BookProof.ChapterF7
open BookProof.ChapterUnboundedPosition


open scoped ENNReal InnerProductSpace


open BookProof.ChapterContinuityUnitaryInfinite (L2Z)

theorem BookProof.ChapterUnboundedPosition.position_not_boundedOperator :
    ¬ ∃ T : L2Z →L[ℂ] L2Z, ∀ psi : mulDomain positionField,
      mulOp positionField psi = T (psi : L2Z) := by sorry
