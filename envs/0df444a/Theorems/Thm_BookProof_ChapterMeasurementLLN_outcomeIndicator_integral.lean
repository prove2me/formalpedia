-- Prove2me | Theorems.Thm_BookProof_ChapterMeasurementLLN_outcomeIndicator_integral
-- name    : BookProof.ChapterMeasurementLLN.outcomeIndicator_integral
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T13:02:40.490976+00:00
-- url     : https://prove2.me/theorems/ce0195e1-99a2-408a-8686-52fc5badb9b4
-- title:
--   `BookProof.ChapterMeasurementLLN.outcomeIndicator_integral` (M : ℕ → Ω → Fin k) (a : Fin k) (hM : Measurable (M 0)) : ∫ ω, outcomeIndicator M a 0 ω ∂μ = (μ {ω | M 0 ω = a}).toReal
-- statement:
--   Prove the following Lean 4 theorem from `ChapterMeasurementLLN`.
--
--   `BookProof.ChapterMeasurementLLN.outcomeIndicator_integral` (M : ℕ → Ω → Fin k) (a : Fin k) (hM : Measurable (M 0)) : ∫ ω, outcomeIndicator M a 0 ω ∂μ = (μ {ω | M 0 ω = a}).toReal
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterMeasurementLLN.outcomeIndicator_integral`.

-- Generated from ChapterMeasurementLLN.lean — theorem BookProof.ChapterMeasurementLLN.outcomeIndicator_integral
import Mathlib
import Definitions.Def_ChapterMeasurementLLN
open BookProof.ChapterMeasurementLLN


open MeasureTheory ProbabilityTheory
open scoped ENNReal


variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {k : ℕ}

theorem BookProof.ChapterMeasurementLLN.outcomeIndicator_integral (M : ℕ → Ω → Fin k) (a : Fin k)
    (hM : Measurable (M 0)) :
    ∫ ω, outcomeIndicator M a 0 ω ∂μ = (μ {ω | M 0 ω = a}).toReal := by sorry
