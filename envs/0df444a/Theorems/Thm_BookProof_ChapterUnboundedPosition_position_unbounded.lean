-- Prove2me | Theorems.Thm_BookProof_ChapterUnboundedPosition_position_unbounded
-- name    : BookProof.ChapterUnboundedPosition.position_unbounded
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-09T05:04:52.20737+00:00
-- url     : https://prove2.me/theorems/c2343fa0-4c82-4357-b3ea-39331812523e
-- title:
--   The Lean 4 theorem `position_unbounded` in the `ChapterUnboundedPosition` chapter of the timepiece formalization
-- statement:
--   Formal statement of `BookProof.ChapterUnboundedPosition.position_unbounded` from the timepiece Lean 4 formalization.
-- source:
--   https://github.com/leonardopedro/timepiece

-- Generated from ChapterUnboundedPosition.lean — theorem BookProof.ChapterUnboundedPosition.position_unbounded
import Mathlib
import Definitions.Def_ChapterUnboundedPosition
import Definitions.Def_ChapterContinuityUnitaryInfinite
import Definitions.Def_ChapterF7
open BookProof.ChapterContinuityUnitaryInfinite
open BookProof.ChapterF7
open BookProof.ChapterUnboundedPosition


open scoped ENNReal InnerProductSpace


open BookProof.ChapterContinuityUnitaryInfinite (L2Z)

theorem BookProof.ChapterUnboundedPosition.position_unbounded :
    ¬ ∃ C : ℝ, ∀ psi : mulDomain positionField,
      ‖mulOp positionField psi‖ ≤ C * ‖(psi : L2Z)‖ := by sorry
