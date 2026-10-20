-- Prove2me | Theorems.Thm_BookProof_ChapterUnboundedPosition_mulOp_symmetric
-- name    : BookProof.ChapterUnboundedPosition.mulOp_symmetric
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-20T01:32:59.500038+00:00
-- url     : https://prove2.me/theorems/328512d4-976b-4415-bea7-899094c873d4
-- title:
--   The Lean 4 theorem `mulOp_symmetric` in the `ChapterUnboundedPosition` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `mulOp_symmetric` in the `ChapterUnboundedPosition` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterUnboundedPosition.lean

-- Generated from ChapterUnboundedPosition.lean — theorem BookProof.ChapterUnboundedPosition.mulOp_symmetric
import Mathlib
import Definitions.Def_ChapterUnboundedPosition
import Definitions.Def_ChapterContinuityUnitaryInfinite
import Definitions.Def_ChapterF7
open BookProof.ChapterContinuityUnitaryInfinite
open BookProof.ChapterF7
open BookProof.ChapterUnboundedPosition


open scoped ENNReal InnerProductSpace


open BookProof.ChapterContinuityUnitaryInfinite (L2Z)

theorem BookProof.ChapterUnboundedPosition.mulOp_symmetric (f : ℤ → ℝ) (psi phi : mulDomain f) :
    ⟪mulOp f psi, (phi : L2Z)⟫_ℂ = ⟪(psi : L2Z), mulOp f phi⟫_ℂ := by sorry
