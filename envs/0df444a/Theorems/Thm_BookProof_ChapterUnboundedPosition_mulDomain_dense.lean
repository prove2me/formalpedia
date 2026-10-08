-- Prove2me | Theorems.Thm_BookProof_ChapterUnboundedPosition_mulDomain_dense
-- name    : BookProof.ChapterUnboundedPosition.mulDomain_dense
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-04T13:51:07.52986+00:00
-- url     : https://prove2.me/theorems/c0a9b2aa-b865-450f-9b99-84ee4f7bc946
-- title:
--   The Lean 4 theorem `mulDomain_dense` in the `ChapterUnboundedPosition` chapter of the timepiece formalization
-- statement:
--   Formal statement of `BookProof.ChapterUnboundedPosition.mulDomain_dense` from the timepiece Lean 4 formalization.
-- source:
--   https://github.com/leonardopedro/timepiece

-- Generated from ChapterUnboundedPosition.lean — theorem BookProof.ChapterUnboundedPosition.mulDomain_dense
import Mathlib
import Definitions.Def_ChapterUnboundedPosition
import Definitions.Def_ChapterContinuityUnitaryInfinite
open BookProof.ChapterContinuityUnitaryInfinite
open BookProof.ChapterUnboundedPosition


open scoped ENNReal InnerProductSpace


open BookProof.ChapterContinuityUnitaryInfinite (L2Z)

theorem BookProof.ChapterUnboundedPosition.mulDomain_dense (f : ℤ → ℝ) : Dense ((mulDomain f : Submodule ℂ L2Z) : Set L2Z) := by sorry
