-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_jump11_original_stopped_grid_initial_event_zero
-- name    : AvramDividend.Classical.avram_ubv_jump11_original_stopped_grid_initial_event_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-08T14:28:32.355905+00:00
-- url     : https://prove2.me/theorems/70ac03da-c58c-45eb-8693-08227c5c99b4
-- title:
--   Original spectrally negative jump stopped-grid count compensation vanishes on initial events
-- statement:
--   For the original Lévy path and filtration, a finite negative-jump cutoff has centred initial-event expectation when compensated jump counts are stopped by a predictable finite-grid survival mask. The event {K>i} must be measurable at the start of each physical grid cell. No auxiliary independent jump process is introduced.
-- source:
--   Original initial-event compensator ad485084 with a physical predictable stopped-grid mask. Advances pure-jump σ=0 positive-clock stopped verification 71fd10ee.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_jump11_original_finitegrid_initial_event_zero
open MeasureTheory Set ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal Nat BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_ubv_jump11_original_stopped_grid_initial_event_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (cut : ℕ)
    (grid : ℕ → ℝ≥0) (hGrid : ∀ i, grid i ≤ grid (i + 1))
    (K : Ω → ℕ)
    (hK : ∀ i, MeasurableSet[𝓕.rightCont (grid i)] {ω : Ω | i < K ω})
    (n : ℕ) (A : Set Ω)
    (hA : MeasurableSet[𝓕.rightCont 0] A) :
    let N : ℕ → Ω → ℝ≥0∞ := fun i ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc (grid i) (grid (i + 1)) ×ˢ Iic (-(1 / ((cut : ℝ) + 1))))
    let r : ℕ → ℝ := fun i =>
      (((grid (i + 1) - grid i : ℝ≥0) : ℝ≥0∞) *
        X.ν (Iic (-(1 / ((cut : ℝ) + 1))))).toReal
    (∫ ω in A, ∑ i ∈ Finset.range n,
      (if i < K ω then (1 : ℝ) else 0) * ((N i ω).toReal - r i) ∂P) = 0 := by sorry
