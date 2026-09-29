-- Prove2me | Theorems.Thm_BookProof_ChapterH1_eigenvalue_mem_numericalRange
-- name    : BookProof.ChapterH1.eigenvalue_mem_numericalRange
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T04:15:20.407153+00:00
-- url     : https://prove2.me/theorems/cdc077fb-9abe-47ee-b6d5-cf39d2270cd3
-- title:
--   (A : E →ₗ[ℂ] E) (l : ℂ) (v : E) (hv : ‖v‖ = 1) (hAv : A v = l • v) : l ∈ numericalRange A
-- statement:
--   Lean 4 theorem `BookProof.ChapterH1.eigenvalue_mem_numericalRange` (module `BookProof.ChapterH1`), source chapter `BookProof/ChapterChapterH1.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterChapterH1.lean

-- Generated from ChapterH1.lean — theorem BookProof.ChapterH1.eigenvalue_mem_numericalRange
import Mathlib
import Definitions.Def_ChapterH1
open BookProof.ChapterH1






open scoped BigOperators
open intervalIntegral


noncomputable section














variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem BookProof.ChapterH1.eigenvalue_mem_numericalRange (A : E →ₗ[ℂ] E) (l : ℂ) (v : E)
    (hv : ‖v‖ = 1) (hAv : A v = l • v) : l ∈ numericalRange A := by sorry
