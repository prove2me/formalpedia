-- Prove2me | Theorems.Thm_BookProof_ChapterG_gauge_generator_excluded_from_algebra
-- name    : BookProof.ChapterG.gauge_generator_excluded_from_algebra
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-08T10:48:57.60734+00:00
-- url     : https://prove2.me/theorems/b58dfaf2-a8d8-4791-aabe-e497b4abea95
-- title:
--   `BookProof.ChapterG.gauge_generator_excluded_from_algebra` {X Y : Type*} (π : X → Y) (h : IsUnconstrainedGaugeFixing π) : ∃ g ∈ gaugeGroup π, ∃ (f : gaugeInvariantSubalgebra ℝ π),
-- statement:
--   Prove the following Lean 4 theorem from `ChapterG`.
--
--   `BookProof.ChapterG.gauge_generator_excluded_from_algebra` {X Y : Type*} (π : X → Y) (h : IsUnconstrainedGaugeFixing π) : ∃ g ∈ gaugeGroup π, ∃ (f : gaugeInvariantSubalgebra ℝ π), (f : X → ℝ) ∘ g ≠ (f : X → ℝ)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterG.gauge_generator_excluded_from_algebra`.

-- Generated from ChapterG.lean — theorem BookProof.ChapterG.gauge_generator_excluded_from_algebra
import Mathlib
import Definitions.Def_ChapterG
import Definitions.Def_ChapterGaugeUnconstrainedSpectrum
open BookProof.ChapterGaugeUnconstrainedSpectrum
open BookProof.ChapterG


open scoped ComplexConjugate InnerProductSpace Matrix
open MeasureTheory

variable {G : Type*} [Group G] [MeasurableSpace G]
variable {μG : Measure G} [IsProbabilityMeasure μG] [μG.IsMulLeftInvariant]
variable {X : Type*} [MulAction G X]
variable {A : Type*} [Ring A]
variable {α β E : Type*} [MeasurableSpace α] [MeasurableSpace β]
  [NormedAddCommGroup E] [NormedSpace ℝ E] {μ : Measure α} {ν : Measure β}
  {p : ENNReal} [Fact (1 ≤ p)]

theorem BookProof.ChapterG.gauge_generator_excluded_from_algebra {X Y : Type*} (π : X → Y)
    (h : IsUnconstrainedGaugeFixing π) :
    ∃ g ∈ gaugeGroup π, ∃ (f : gaugeInvariantSubalgebra ℝ π),
      (f : X → ℝ) ∘ g ≠ (f : X → ℝ) := by sorry
