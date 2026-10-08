-- Prove2me | Theorems.Thm_BookProof_ChapterCoherentOverlapComplex_bornWeightC_sum_one
-- name    : BookProof.ChapterCoherentOverlapComplex.bornWeightC_sum_one
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T22:02:26.928576+00:00
-- url     : https://prove2.me/theorems/333e4b55-ceea-444e-8666-69ddec34af03
-- title:
--   `BookProof.ChapterCoherentOverlapComplex.bornWeightC_sum_one` (q : EuclideanSpace ℂ (Fin n)) (k : Fin m → EuclideanSpace ℂ (Fin n)) (j₀ : Fin m) : ∑ j, bornWeightC q k j = 1
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCoherentOverlapComplex`.
--
--   `BookProof.ChapterCoherentOverlapComplex.bornWeightC_sum_one` (q : EuclideanSpace ℂ (Fin n)) (k : Fin m → EuclideanSpace ℂ (Fin n)) (j₀ : Fin m) : ∑ j, bornWeightC q k j = 1
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterCoherentOverlapComplex.bornWeightC_sum_one`.

-- Generated from ChapterCoherentOverlapComplex.lean — theorem BookProof.ChapterCoherentOverlapComplex.bornWeightC_sum_one
import Mathlib
import Definitions.Def_ChapterCoherentOverlapComplex
open BookProof.ChapterCoherentOverlapComplex


open scoped BigOperators

noncomputable section


variable {n m : ℕ}

theorem BookProof.ChapterCoherentOverlapComplex.bornWeightC_sum_one (q : EuclideanSpace ℂ (Fin n))
    (k : Fin m → EuclideanSpace ℂ (Fin n)) (j₀ : Fin m) :
    ∑ j, bornWeightC q k j = 1 := by sorry
