-- Prove2me | Theorems.Thm_BookProof_ChapterCoherentOverlapComplex_coherentOverlapC_eq_modulus_mul_phase
-- name    : BookProof.ChapterCoherentOverlapComplex.coherentOverlapC_eq_modulus_mul_phase
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T22:00:55.855786+00:00
-- url     : https://prove2.me/theorems/d853cea6-d3b2-4785-89ff-1808e3670723
-- title:
--   `BookProof.ChapterCoherentOverlapComplex.coherentOverlapC_eq_modulus_mul_phase` (q k : EuclideanSpace ℂ (Fin n)) : coherentOverlapC q k = (Real.exp (-‖q‖ ^ 2 / 2 - ‖k‖ ^ 2 / 2 + (i
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCoherentOverlapComplex`.
--
--   `BookProof.ChapterCoherentOverlapComplex.coherentOverlapC_eq_modulus_mul_phase` (q k : EuclideanSpace ℂ (Fin n)) : coherentOverlapC q k = (Real.exp (-‖q‖ ^ 2 / 2 - ‖k‖ ^ 2 / 2 + (inner ℂ q k : ℂ).re) : ℂ) * Complex.exp (((inner ℂ q k : ℂ).im : ℂ) * Complex.I)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterCoherentOverlapComplex.coherentOverlapC_eq_modulus_mul_phase`.

-- Generated from ChapterCoherentOverlapComplex.lean — theorem BookProof.ChapterCoherentOverlapComplex.coherentOverlapC_eq_modulus_mul_phase
import Mathlib
import Definitions.Def_ChapterCoherentOverlapComplex
open BookProof.ChapterCoherentOverlapComplex


open scoped BigOperators

noncomputable section


variable {n m : ℕ}

theorem BookProof.ChapterCoherentOverlapComplex.coherentOverlapC_eq_modulus_mul_phase (q k : EuclideanSpace ℂ (Fin n)) :
    coherentOverlapC q k =
      (Real.exp (-‖q‖ ^ 2 / 2 - ‖k‖ ^ 2 / 2 + (inner ℂ q k : ℂ).re) : ℂ) *
        Complex.exp (((inner ℂ q k : ℂ).im : ℂ) * Complex.I) := by sorry
