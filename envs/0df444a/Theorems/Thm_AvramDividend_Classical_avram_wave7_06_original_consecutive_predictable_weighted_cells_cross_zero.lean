-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_consecutive_predictable_weighted_cells_cross_zero
-- name    : AvramDividend.Classical.avram_wave7_06_original_consecutive_predictable_weighted_cells_cross_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T18:25:32.269029+00:00
-- url     : https://prove2.me/theorems/3f394237-3334-4f2c-ac10-5f84f0085650
-- title:
--   Consecutive original-filtration predictable weighted centred Levy cells have zero cross expectation
-- statement:
--   For actual source Levy X and its original filtration, an F_s-predictable weight on the first interval and F_(s+u)-predictable weight on the second give zero cross expectation after centring both source increments. Explicit integrability of the earlier weighted cell multiplied by the later weight makes the future-centred L1 factorisation legitimate. No auxiliary process or Poisson sample space.
-- source:
--   W7-06 original stopped predictable finite-grid L1/L2 cross-term for the martingale isometry; exact source X, P and filtration.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Filter Set Topology ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_06_original_consecutive_predictable_weighted_cells_cross_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (s u v : ℝ≥0)
    (W₀ W₁ : Ω → ℝ)
    (hW₀ : Measurable[𝓕 s] W₀)
    (hW₁ : Measurable[𝓕 (s + u)] W₁)
    (hXI : Integrable (X.X v) P)
    (hProduct : Integrable (fun ω =>
      (W₀ ω * (X.X (s + u) ω - X.X s ω -
        (∫ η, X.X u η ∂P))) * W₁ ω) P) :
    (∫ ω, ((W₀ ω * (X.X (s + u) ω - X.X s ω -
      (∫ η, X.X u η ∂P))) * W₁ ω) *
      (X.X (s + u + v) ω - X.X (s + u) ω -
        (∫ η, X.X v η ∂P)) ∂P) = 0 := by sorry
