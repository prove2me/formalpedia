-- Prove2me | Theorems.Thm_BookProof_ChapterShannonSampling_integral_haar_eq_real
-- name    : BookProof.ChapterShannonSampling.integral_haar_eq_real
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T12:24:12.777099+00:00
-- url     : https://prove2.me/theorems/0ffc7133-9d5d-46b2-a28e-1c549cf72416
-- title:
--   `BookProof.ChapterShannonSampling.integral_haar_eq_real` (g : AddCircle T → ℝ) : T * ∫ z : AddCircle T, g z ∂haarAddCircle = ∫ ξ in (-(T / 2))..(-(T / 2) + T), g ξ
-- statement:
--   Prove the following Lean 4 theorem from `ChapterShannonSampling`.
--
--   `BookProof.ChapterShannonSampling.integral_haar_eq_real` (g : AddCircle T → ℝ) : T * ∫ z : AddCircle T, g z ∂haarAddCircle = ∫ ξ in (-(T / 2))..(-(T / 2) + T), g ξ
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterShannonSampling.integral_haar_eq_real`.

-- Generated from ChapterShannonSampling.lean — theorem BookProof.ChapterShannonSampling.integral_haar_eq_real
import Mathlib
import Definitions.Def_ChapterShannonSampling
open BookProof.ChapterShannonSampling



open MeasureTheory Complex AddCircle intervalIntegral Set
open scoped Real ComplexConjugate

variable {T : ℝ} [hT : Fact (0 < T)]

theorem BookProof.ChapterShannonSampling.integral_haar_eq_real (g : AddCircle T → ℝ) :
    T * ∫ z : AddCircle T, g z ∂haarAddCircle
      = ∫ ξ in (-(T / 2))..(-(T / 2) + T), g ξ := by sorry
