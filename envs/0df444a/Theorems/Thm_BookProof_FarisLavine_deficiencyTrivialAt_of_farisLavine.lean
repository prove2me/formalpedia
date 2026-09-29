-- Prove2me | Theorems.Thm_BookProof_FarisLavine_deficiencyTrivialAt_of_farisLavine
-- name    : BookProof.FarisLavine.deficiencyTrivialAt_of_farisLavine
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T23:23:19.30073+00:00
-- url     : https://prove2.me/theorems/635dd962-897a-49ff-8a4f-194a82f89b3c
-- title:
--   The Lean 4 theorem `deficiencyTrivialAt_of_farisLavine` in the `ChapterFarisLavineCore` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `deficiencyTrivialAt_of_farisLavine` in the `ChapterFarisLavineCore` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterFarisLavineCore.lean

-- Generated from ChapterFarisLavineCore.lean — theorem BookProof.FarisLavine.deficiencyTrivialAt_of_farisLavine
import Mathlib
import Definitions.Def_ChapterFarisLavineCore
open BookProof.FarisLavine












variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D : Submodule ℂ F}

theorem BookProof.FarisLavine.deficiencyTrivialAt_of_farisLavine
    (H N : D →ₗ[ℂ] F) (c d : ℝ)
    (hH : SymmetricOn D H) (hN : SymmetricOn D N)
    (hc : 0 ≤ c)
    (hNpos : ∀ x : D, 0 ≤ quadForm N x)
    (hNsurj : ∀ f : F, ∃ x : D, N x + (x : F) = f)
    (hcomm : ∀ x : D, |commForm H N x| ≤ c * quadForm N x)
    (hd : c < 2 * |d|) :
    DeficiencyTrivialAt D H ((d : ℂ) * Complex.I) := by sorry
