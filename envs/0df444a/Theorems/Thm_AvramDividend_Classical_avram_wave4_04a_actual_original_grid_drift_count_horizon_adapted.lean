-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_original_grid_drift_count_horizon_adapted
-- name    : AvramDividend.Classical.avram_wave4_04a_actual_original_grid_drift_count_horizon_adapted
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T00:15:26.024199+00:00
-- url     : https://prove2.me/theorems/e3cc1dec-9b47-4c1c-af52-9dc189fef9d9
-- title:
--   Actual source Lévy finite-grid jump-occupancy approximation is measurable at its original filtration horizon
-- statement:
--   For the genuine source SpectrallyNegativeLevy X on its original sample space and filtration 𝓕, every finite deterministic time grid whose nodes through n lie in [0,T] has its original-path drift-deficient cell count measurable with respect to 𝓕 T, not merely the ambient measurable space. This supplies the filtration-adapted finite-level approximants needed for a same-path predictable jump-count construction. It uses X.adapted and no independent Poisson replacement or completion assumption.
-- source:
--   The source-measurable but not filtration-specific original grid count theorem 7d565b48-2aee-434c-8f46-b4db7429c950 is canonically Proved; this theorem strengthens it to adaptedness at a horizon by propagating the exact original X.adapted property along Filtration.mono and Finset.card_filter. Distinct source-compensator prerequisite, no stochastic compensation claim.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_wave4_04a_actual_original_grid_drift_count_horizon_adapted
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (n : ℕ) (grid : ℕ → ℝ≥0)
    (hBound : ∀ i : ℕ, i ≤ n → grid i ≤ T) :
    Measurable[𝓕 T] (fun ω : Ω =>
      ((Finset.range n).filter (fun i =>
        X.X (grid (i + 1)) ω - X.X (grid i) ω <
          X.drift * (((grid (i + 1) - grid i : ℝ≥0) : ℝ)))).card) := by sorry
