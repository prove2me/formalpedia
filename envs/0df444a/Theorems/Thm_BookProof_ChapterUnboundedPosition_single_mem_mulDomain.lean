-- Prove2me | Theorems.Thm_BookProof_ChapterUnboundedPosition_single_mem_mulDomain
-- name    : BookProof.ChapterUnboundedPosition.single_mem_mulDomain
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-04T13:51:17.902805+00:00
-- url     : https://prove2.me/theorems/1ec2e18a-3359-43f0-99c9-3d8ac3d597fd
-- title:
--   The Lean 4 theorem `single_mem_mulDomain` in the `ChapterUnboundedPosition` chapter of the timepiece formalization
-- statement:
--   Formal statement of `BookProof.ChapterUnboundedPosition.single_mem_mulDomain` from the timepiece Lean 4 formalization.
-- source:
--   https://github.com/leonardopedro/timepiece

-- Generated from ChapterUnboundedPosition.lean — theorem BookProof.ChapterUnboundedPosition.single_mem_mulDomain
import Mathlib
import Definitions.Def_ChapterUnboundedPosition
import Definitions.Def_ChapterContinuityUnitaryInfinite
open BookProof.ChapterContinuityUnitaryInfinite
open BookProof.ChapterUnboundedPosition


open scoped ENNReal InnerProductSpace


open BookProof.ChapterContinuityUnitaryInfinite (L2Z)

theorem BookProof.ChapterUnboundedPosition.single_mem_mulDomain (f : ℤ → ℝ) (n : ℤ) (c : ℂ) :
    lp.single 2 n c ∈ mulDomain f := by sorry
