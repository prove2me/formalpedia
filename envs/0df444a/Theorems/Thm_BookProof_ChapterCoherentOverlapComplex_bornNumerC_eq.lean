-- Prove2me | Theorems.Thm_BookProof_ChapterCoherentOverlapComplex_bornNumerC_eq
-- name    : BookProof.ChapterCoherentOverlapComplex.bornNumerC_eq
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T22:01:34.930016+00:00
-- url     : https://prove2.me/theorems/e986c11b-1cc4-4cb0-a987-93818cab8328
-- title:
--   `BookProof.ChapterCoherentOverlapComplex.bornNumerC_eq` (q k : EuclideanSpace ℂ (Fin n)) : bornNumerC q k = Real.exp (-‖q‖ ^ 2) * Real.exp (-‖k‖ ^ 2) * Real.exp (2 * (inner ℂ q k :
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCoherentOverlapComplex`.
--
--   `BookProof.ChapterCoherentOverlapComplex.bornNumerC_eq` (q k : EuclideanSpace ℂ (Fin n)) : bornNumerC q k = Real.exp (-‖q‖ ^ 2) * Real.exp (-‖k‖ ^ 2) * Real.exp (2 * (inner ℂ q k : ℂ).re)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterCoherentOverlapComplex.bornNumerC_eq`.

-- Generated from ChapterCoherentOverlapComplex.lean — theorem BookProof.ChapterCoherentOverlapComplex.bornNumerC_eq
import Mathlib
import Definitions.Def_ChapterCoherentOverlapComplex
open BookProof.ChapterCoherentOverlapComplex


open scoped BigOperators

noncomputable section


variable {n m : ℕ}

theorem BookProof.ChapterCoherentOverlapComplex.bornNumerC_eq (q k : EuclideanSpace ℂ (Fin n)) :
    bornNumerC q k =
      Real.exp (-‖q‖ ^ 2) * Real.exp (-‖k‖ ^ 2)
        * Real.exp (2 * (inner ℂ q k : ℂ).re) := by sorry
