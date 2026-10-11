-- Prove2me | Theorems.Thm_BookProof_ChapterShannonSampling_bandSignal_eq_circle_integral
-- name    : BookProof.ChapterShannonSampling.bandSignal_eq_circle_integral
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T12:22:43.921749+00:00
-- url     : https://prove2.me/theorems/168480d5-e7ff-4b36-b903-1e354196a117
-- title:
--   `BookProof.ChapterShannonSampling.bandSignal_eq_circle_integral` (F : AddCircle T → ℂ) (x : ℝ) : bandSignal (T := T) F x = ∫ z : AddCircle T, conj (kern (T := T) x z) * F z
-- statement:
--   Prove the following Lean 4 theorem from `ChapterShannonSampling`.
--
--   `BookProof.ChapterShannonSampling.bandSignal_eq_circle_integral` (F : AddCircle T → ℂ) (x : ℝ) : bandSignal (T := T) F x = ∫ z : AddCircle T, conj (kern (T := T) x z) * F z
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterShannonSampling.bandSignal_eq_circle_integral`.

-- Generated from ChapterShannonSampling.lean — theorem BookProof.ChapterShannonSampling.bandSignal_eq_circle_integral
import Mathlib
import Definitions.Def_ChapterShannonSampling
open BookProof.ChapterShannonSampling



open MeasureTheory Complex AddCircle intervalIntegral Set
open scoped Real ComplexConjugate

variable {T : ℝ} [hT : Fact (0 < T)]

theorem BookProof.ChapterShannonSampling.bandSignal_eq_circle_integral (F : AddCircle T → ℂ) (x : ℝ) :
    bandSignal (T := T) F x = ∫ z : AddCircle T, conj (kern (T := T) x z) * F z := by sorry
