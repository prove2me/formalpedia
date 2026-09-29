-- Prove2me | Theorems.Thm_BookProof_FarisLavine_deficiencyTrivialAt_of_dense_range
-- name    : BookProof.FarisLavine.deficiencyTrivialAt_of_dense_range
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T23:23:29.285089+00:00
-- url     : https://prove2.me/theorems/9b88ae4a-cf0d-4c21-b11b-da5477a7dd88
-- title:
--   The Lean 4 theorem `deficiencyTrivialAt_of_dense_range` in the `ChapterFarisLavineCore` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `deficiencyTrivialAt_of_dense_range` in the `ChapterFarisLavineCore` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterFarisLavineCore.lean

-- Generated from ChapterFarisLavineCore.lean — theorem BookProof.FarisLavine.deficiencyTrivialAt_of_dense_range
import Mathlib
import Definitions.Def_ChapterFarisLavineCore
open BookProof.FarisLavine












variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D : Submodule ℂ F}

theorem BookProof.FarisLavine.deficiencyTrivialAt_of_dense_range [CompleteSpace F] (H : D →ₗ[ℂ] F)
    (hH : SymmetricOn D H) (e : ℝ) (he : e ≠ 0) (σ : ℂ) (hσ : σ.im ≠ 0)
    (hdense : Dense (Set.range fun x : D => H x - ((e : ℂ) * Complex.I) • (x : F)))
    (hdef : DeficiencyTrivialAt D H ((e : ℂ) * Complex.I)) :
    DeficiencyTrivialAt D H σ := by sorry
