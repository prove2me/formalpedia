-- Prove2me | Theorems.Thm_BookProof_FarisLavine_dense_range_of_deficiencyTrivialAt
-- name    : BookProof.FarisLavine.dense_range_of_deficiencyTrivialAt
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T18:17:30.149138+00:00
-- url     : https://prove2.me/theorems/c5204405-076d-441a-939b-9670aa35929a
-- title:
--   The Lean 4 theorem `dense_range_of_deficiencyTrivialAt` in the `ChapterFarisLavineCore` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `dense_range_of_deficiencyTrivialAt` in the `ChapterFarisLavineCore` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterFarisLavineCore.lean

-- Generated from ChapterFarisLavineCore.lean — theorem BookProof.FarisLavine.dense_range_of_deficiencyTrivialAt
import Mathlib
import Definitions.Def_ChapterFarisLavineCore
open BookProof.FarisLavine












variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D : Submodule ℂ F}

theorem BookProof.FarisLavine.dense_range_of_deficiencyTrivialAt [CompleteSpace F] (H : D →ₗ[ℂ] F) (w₀ : ℂ)
    (h : DeficiencyTrivialAt D H (starRingEnd ℂ w₀)) :
    Dense (Set.range fun x : D => H x - w₀ • (x : F)) := by sorry
