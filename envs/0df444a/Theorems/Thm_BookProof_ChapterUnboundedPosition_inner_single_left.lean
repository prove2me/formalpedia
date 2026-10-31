-- Prove2me | Theorems.Thm_BookProof_ChapterUnboundedPosition_inner_single_left
-- name    : BookProof.ChapterUnboundedPosition.inner_single_left
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-30T12:06:42.700605+00:00
-- url     : https://prove2.me/theorems/9d2cbf69-24ed-4c80-bac8-912c28b69dd9
-- title:
--   The Lean 4 theorem `inner_single_left` in the `ChapterUnboundedPosition` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `inner_single_left` in the `ChapterUnboundedPosition` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterUnboundedPosition.lean

-- Generated from ChapterUnboundedPosition.lean — theorem BookProof.ChapterUnboundedPosition.inner_single_left
import Mathlib
import Definitions.Def_ChapterUnboundedPosition
import Definitions.Def_ChapterContinuityUnitaryInfinite
open BookProof.ChapterContinuityUnitaryInfinite
open BookProof.ChapterUnboundedPosition


open scoped ENNReal InnerProductSpace


open BookProof.ChapterContinuityUnitaryInfinite (L2Z)

theorem BookProof.ChapterUnboundedPosition.inner_single_left (phi : L2Z) (k : ℤ) (c : ℂ) :
    ⟪(lp.single 2 k c : L2Z), phi⟫_ℂ = (starRingEnd ℂ) c * (phi : ℤ → ℂ) k := by sorry
