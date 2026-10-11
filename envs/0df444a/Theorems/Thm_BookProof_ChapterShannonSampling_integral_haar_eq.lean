-- Prove2me | Theorems.Thm_BookProof_ChapterShannonSampling_integral_haar_eq
-- name    : BookProof.ChapterShannonSampling.integral_haar_eq
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T12:22:38.795979+00:00
-- url     : https://prove2.me/theorems/df8be7c8-a2d6-494b-9515-eca599360a8b
-- title:
--   `BookProof.ChapterShannonSampling.integral_haar_eq` (g : AddCircle T → ℂ) : (T : ℂ) * ∫ z : AddCircle T, g z ∂haarAddCircle = ∫ ξ in (-(T / 2))..(-(T / 2) + T), g ξ
-- statement:
--   Prove the following Lean 4 theorem from `ChapterShannonSampling`.
--
--   `BookProof.ChapterShannonSampling.integral_haar_eq` (g : AddCircle T → ℂ) : (T : ℂ) * ∫ z : AddCircle T, g z ∂haarAddCircle = ∫ ξ in (-(T / 2))..(-(T / 2) + T), g ξ
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterShannonSampling.integral_haar_eq`.

-- Generated from ChapterShannonSampling.lean — theorem BookProof.ChapterShannonSampling.integral_haar_eq
import Mathlib
import Definitions.Def_ChapterShannonSampling
open BookProof.ChapterShannonSampling



open MeasureTheory Complex AddCircle intervalIntegral Set
open scoped Real ComplexConjugate

variable {T : ℝ} [hT : Fact (0 < T)]

theorem BookProof.ChapterShannonSampling.integral_haar_eq (g : AddCircle T → ℂ) :
    (T : ℂ) * ∫ z : AddCircle T, g z ∂haarAddCircle
      = ∫ ξ in (-(T / 2))..(-(T / 2) + T), g ξ := by sorry
