-- Prove2me | Theorems.Thm_BookProof_ChapterUnboundedPosition_mem_mulDomain_iff
-- name    : BookProof.ChapterUnboundedPosition.mem_mulDomain_iff
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-30T12:06:42.291999+00:00
-- url     : https://prove2.me/theorems/5f18e3aa-266f-43de-88e4-2d46bbacd07c
-- title:
--   The Lean 4 theorem `mem_mulDomain_iff` in the `ChapterUnboundedPosition` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `mem_mulDomain_iff` in the `ChapterUnboundedPosition` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterUnboundedPosition.lean

-- Generated from ChapterUnboundedPosition.lean — theorem BookProof.ChapterUnboundedPosition.mem_mulDomain_iff
import Mathlib
import Definitions.Def_ChapterUnboundedPosition
import Definitions.Def_ChapterContinuityUnitaryInfinite
open BookProof.ChapterContinuityUnitaryInfinite
open BookProof.ChapterUnboundedPosition


open scoped ENNReal InnerProductSpace


open BookProof.ChapterContinuityUnitaryInfinite (L2Z)

theorem BookProof.ChapterUnboundedPosition.mem_mulDomain_iff (f : ℤ → ℝ) (psi : L2Z) :
    psi ∈ mulDomain f ↔ Memℓp (fun k => (f k : ℂ) * (psi : ℤ → ℂ) k) 2 := by sorry
