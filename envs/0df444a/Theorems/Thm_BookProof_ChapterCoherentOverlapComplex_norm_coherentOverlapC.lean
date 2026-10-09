-- Prove2me | Theorems.Thm_BookProof_ChapterCoherentOverlapComplex_norm_coherentOverlapC
-- name    : BookProof.ChapterCoherentOverlapComplex.norm_coherentOverlapC
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T22:00:58.484076+00:00
-- url     : https://prove2.me/theorems/43debf4d-2fbf-4c78-b223-6f9570a1902d
-- title:
--   `BookProof.ChapterCoherentOverlapComplex.norm_coherentOverlapC` (q k : EuclideanSpace ℂ (Fin n)) : ‖coherentOverlapC q k‖ = Real.exp (-‖q‖ ^ 2 / 2 - ‖k‖ ^ 2 / 2 + (inner ℂ q k : ℂ)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCoherentOverlapComplex`.
--
--   `BookProof.ChapterCoherentOverlapComplex.norm_coherentOverlapC` (q k : EuclideanSpace ℂ (Fin n)) : ‖coherentOverlapC q k‖ = Real.exp (-‖q‖ ^ 2 / 2 - ‖k‖ ^ 2 / 2 + (inner ℂ q k : ℂ).re)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterCoherentOverlapComplex.norm_coherentOverlapC`.

-- Generated from ChapterCoherentOverlapComplex.lean — theorem BookProof.ChapterCoherentOverlapComplex.norm_coherentOverlapC
import Mathlib
import Definitions.Def_ChapterCoherentOverlapComplex
open BookProof.ChapterCoherentOverlapComplex


open scoped BigOperators

noncomputable section


variable {n m : ℕ}

theorem BookProof.ChapterCoherentOverlapComplex.norm_coherentOverlapC (q k : EuclideanSpace ℂ (Fin n)) :
    ‖coherentOverlapC q k‖
      = Real.exp (-‖q‖ ^ 2 / 2 - ‖k‖ ^ 2 / 2 + (inner ℂ q k : ℂ).re) := by sorry
