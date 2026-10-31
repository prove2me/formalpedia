-- Prove2me | Theorems.Thm_BookProof_ChapterUnboundedPosition_sum_single_mem_mulDomain
-- name    : BookProof.ChapterUnboundedPosition.sum_single_mem_mulDomain
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-30T12:06:43.610134+00:00
-- url     : https://prove2.me/theorems/9eb27931-e4ef-461d-a9a0-8b446d42dbcd
-- title:
--   The Lean 4 theorem `sum_single_mem_mulDomain` in the `ChapterUnboundedPosition` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `sum_single_mem_mulDomain` in the `ChapterUnboundedPosition` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterUnboundedPosition.lean

-- Generated from ChapterUnboundedPosition.lean — theorem BookProof.ChapterUnboundedPosition.sum_single_mem_mulDomain
import Mathlib
import Definitions.Def_ChapterUnboundedPosition
import Definitions.Def_ChapterContinuityUnitaryInfinite
open BookProof.ChapterContinuityUnitaryInfinite
open BookProof.ChapterUnboundedPosition


open scoped ENNReal InnerProductSpace


open BookProof.ChapterContinuityUnitaryInfinite (L2Z)

theorem BookProof.ChapterUnboundedPosition.sum_single_mem_mulDomain (f : ℤ → ℝ) (psi : L2Z) (s : Finset ℤ) :
    (∑ i ∈ s, lp.single 2 i ((psi : ℤ → ℂ) i)) ∈ mulDomain f := by sorry
