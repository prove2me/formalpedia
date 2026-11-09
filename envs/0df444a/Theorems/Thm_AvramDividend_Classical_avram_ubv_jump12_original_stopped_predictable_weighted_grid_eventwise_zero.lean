-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_jump12_original_stopped_predictable_weighted_grid_eventwise_zero
-- name    : AvramDividend.Classical.avram_ubv_jump12_original_stopped_predictable_weighted_grid_eventwise_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-08T14:42:19.062447+00:00
-- url     : https://prove2.me/theorems/a47dfa10-feda-4eee-a5e9-55780bad8c10
-- title:
--   Original stopped predictable weighted negative-jump finite-grid compensation vanishes on each initial event
-- statement:
--   For the original spectrally negative Lévy process and any right-continuous stopping clock, the finite-grid compensated negative jump sum, weighted by bounded coefficients measurable at each cell start and further masked by survival of the stopping clock, integrates to zero over every initial-filtration event. This combines the already proved all-initial-event finite-grid compensated cancellation with the actual stopped predictable mask.
-- source:
--   Original source ad485084 and stopping time measurability; needed for the true stopped Taylor generator passage toward 0b1a879a.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_jump11_original_finitegrid_initial_event_zero
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Nat BigOperators

theorem AvramDividend.Classical.avram_ubv_jump12_original_stopped_predictable_weighted_grid_eventwise_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (cut : ℕ)
    (grid : ℕ → ℝ≥0) (hGrid : ∀ i, grid i ≤ grid (i + 1))
    (H : ℕ → Ω → ℝ)
    (hH : ∀ i, StronglyMeasurable[𝓕.rightCont (grid i)] (H i))
    (L : ℝ) (hBound : ∀ i ω, |H i ω| ≤ L)
    (τ : Ω → ℝ≥0)
    (hτstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
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
    let Z : ℕ → Ω → ℝ := fun i ω =>
      (if grid i < τ ω then H i ω else 0) * ((N i ω).toReal - r i)
    (∫ ω in A, ∑ i ∈ Finset.range n, Z i ω ∂P) = 0 := by sorry
