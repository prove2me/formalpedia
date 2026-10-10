-- Prove2me | Theorems.Thm_BookProof_ChapterMeasurementLLN_measurement_average_tendsto
-- name    : BookProof.ChapterMeasurementLLN.measurement_average_tendsto
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T13:02:56.690994+00:00
-- url     : https://prove2.me/theorems/c7c91e37-aa91-4e9f-bf2a-43b0e8709c05
-- title:
--   `BookProof.ChapterMeasurementLLN.measurement_average_tendsto` (M : ℕ → Ω → Fin k) (f : Fin k → ℝ) (hmeas : ∀ i, Measurable (M i)) (hindep : Pairwise (fun i j => IndepFun (M i) (M j
-- statement:
--   Prove the following Lean 4 theorem from `ChapterMeasurementLLN`.
--
--   `BookProof.ChapterMeasurementLLN.measurement_average_tendsto` (M : ℕ → Ω → Fin k) (f : Fin k → ℝ) (hmeas : ∀ i, Measurable (M i)) (hindep : Pairwise (fun i j => IndepFun (M i) (M j) μ)) (hident : ∀ i, IdentDistrib (M i) (M 0) μ μ) : ∀ᵐ ω ∂μ, Filter.Tendsto (fun n => (∑ i ∈ Finset.range n, f (M i ω)) / n) Filter.atTop (nhds (∫ ω, f (M 0 ω) ∂μ))
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterMeasurementLLN.measurement_average_tendsto`.

-- Generated from ChapterMeasurementLLN.lean — theorem BookProof.ChapterMeasurementLLN.measurement_average_tendsto
import Mathlib
import Definitions.Def_ChapterMeasurementLLN
open BookProof.ChapterMeasurementLLN


open MeasureTheory ProbabilityTheory
open scoped ENNReal


variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {k : ℕ}

theorem BookProof.ChapterMeasurementLLN.measurement_average_tendsto (M : ℕ → Ω → Fin k) (f : Fin k → ℝ)
    (hmeas : ∀ i, Measurable (M i))
    (hindep : Pairwise (fun i j => IndepFun (M i) (M j) μ))
    (hident : ∀ i, IdentDistrib (M i) (M 0) μ μ) :
    ∀ᵐ ω ∂μ, Filter.Tendsto
      (fun n => (∑ i ∈ Finset.range n, f (M i ω)) / n)
      Filter.atTop (nhds (∫ ω, f (M 0 ω) ∂μ)) := by sorry
