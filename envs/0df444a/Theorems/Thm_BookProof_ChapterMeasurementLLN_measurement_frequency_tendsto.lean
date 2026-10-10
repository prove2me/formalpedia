-- Prove2me | Theorems.Thm_BookProof_ChapterMeasurementLLN_measurement_frequency_tendsto
-- name    : BookProof.ChapterMeasurementLLN.measurement_frequency_tendsto
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T13:03:08.329302+00:00
-- url     : https://prove2.me/theorems/bce8a0bb-95c4-4164-82f2-58fe7e0c1a4d
-- title:
--   `BookProof.ChapterMeasurementLLN.measurement_frequency_tendsto` (M : ℕ → Ω → Fin k) (a : Fin k) (hmeas : ∀ i, Measurable (M i)) (hindep : Pairwise (fun i j => IndepFun (M i) (M j)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterMeasurementLLN`.
--
--   `BookProof.ChapterMeasurementLLN.measurement_frequency_tendsto` (M : ℕ → Ω → Fin k) (a : Fin k) (hmeas : ∀ i, Measurable (M i)) (hindep : Pairwise (fun i j => IndepFun (M i) (M j) μ)) (hident : ∀ i, IdentDistrib (M i) (M 0) μ μ) : ∀ᵐ ω ∂μ, Filter.Tendsto (fun n => (∑ i ∈ Finset.range n, outcomeIndicator M a i ω) / n) Filter.atTop (nhds (μ {ω | M 0 ω = a}).toReal)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterMeasurementLLN.measurement_frequency_tendsto`.

-- Generated from ChapterMeasurementLLN.lean — theorem BookProof.ChapterMeasurementLLN.measurement_frequency_tendsto
import Mathlib
import Definitions.Def_ChapterMeasurementLLN
open BookProof.ChapterMeasurementLLN


open MeasureTheory ProbabilityTheory
open scoped ENNReal


variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {k : ℕ}

theorem BookProof.ChapterMeasurementLLN.measurement_frequency_tendsto (M : ℕ → Ω → Fin k) (a : Fin k)
    (hmeas : ∀ i, Measurable (M i))
    (hindep : Pairwise (fun i j => IndepFun (M i) (M j) μ))
    (hident : ∀ i, IdentDistrib (M i) (M 0) μ μ) :
    ∀ᵐ ω ∂μ, Filter.Tendsto
      (fun n => (∑ i ∈ Finset.range n, outcomeIndicator M a i ω) / n)
      Filter.atTop (nhds (μ {ω | M 0 ω = a}).toReal) := by sorry
