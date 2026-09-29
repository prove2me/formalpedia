-- Prove2me | Theorems.Thm_BookProof_YangMillsFriedrichsLimit_not_mem_span_of_repr_ne_zero
-- name    : BookProof.YangMillsFriedrichsLimit.not_mem_span_of_repr_ne_zero
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T19:19:36.980003+00:00
-- url     : https://prove2.me/theorems/29fd97a4-710f-40ca-95cc-cae62086de30
-- title:
--   The Lean 4 theorem `not_mem_span_of_repr_ne_zero` in the `ChapterYangMillsFriedrichsLimit` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `not_mem_span_of_repr_ne_zero` in the `ChapterYangMillsFriedrichsLimit` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterYangMillsFriedrichsLimit.lean

-- Generated from ChapterYangMillsFriedrichsLimit.lean — theorem BookProof.YangMillsFriedrichsLimit.not_mem_span_of_repr_ne_zero
import Mathlib
import Definitions.Def_ChapterYangMillsFriedrichsLimit
open BookProof.YangMillsFriedrichsLimit








open BookProof.FarisLavine BookProof.YangMillsFriedrichs



variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]











open scoped InnerProductSpace ENNReal

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

theorem BookProof.YangMillsFriedrichsLimit.not_mem_span_of_repr_ne_zero (b : HilbertBasis ℕ ℂ F)
    (x : F) (hx : ∀ i, b.repr x i ≠ 0) : x ∉ Submodule.span ℂ (Set.range b) := by sorry
