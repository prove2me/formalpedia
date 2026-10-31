-- Prove2me | Theorems.Thm_BookProof_ChapterUnboundedPosition_mulOp_single
-- name    : BookProof.ChapterUnboundedPosition.mulOp_single
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-31T01:57:31.977494+00:00
-- url     : https://prove2.me/theorems/9d21e545-ad53-4635-85ee-000aee7f0f68
-- title:
--   The Lean 4 theorem `mulOp_single` in the `ChapterUnboundedPosition` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `mulOp_single` in the `ChapterUnboundedPosition` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterUnboundedPosition.lean

-- Generated from ChapterUnboundedPosition.lean — theorem BookProof.ChapterUnboundedPosition.mulOp_single
import Mathlib
import Definitions.Def_ChapterUnboundedPosition
import Theorems.Thm_BookProof_ChapterUnboundedPosition_single_mem_mulDomain
import Definitions.Def_ChapterContinuityUnitaryInfinite
import Definitions.Def_ChapterF7
import Definitions.Def_ChapterF7
open BookProof.ChapterContinuityUnitaryInfinite
open BookProof.ChapterF7
open BookProof.ChapterUnboundedPosition


open scoped ENNReal InnerProductSpace


open BookProof.ChapterContinuityUnitaryInfinite (L2Z)

theorem BookProof.ChapterUnboundedPosition.mulOp_single (f : ℤ → ℝ) (n : ℤ) (c : ℂ) :
    mulOp f ⟨lp.single 2 n c, single_mem_mulDomain f n c⟩ = lp.single 2 n ((f n : ℂ) * c) := by sorry
