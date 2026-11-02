-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_01_bv_actual_intrinsic_total_count_lintegral_equals_source_levy_rate
-- name    : AvramDividend.Classical.avram_wave5_01_bv_actual_intrinsic_total_count_lintegral_equals_source_levy_rate
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T19:12:15.063866+00:00
-- url     : https://prove2.me/theorems/d8534d75-736f-49a0-ac4b-f76b9ed6de55
-- title:
--   Original BV Lévy literal jump-count lintegral equals finite source Lévy total rate
-- statement:
--   For the genuine original SpectrallyNegativeLevy P 𝓕 with bounded variation and finite negative Lévy mass, and any positive finite horizon equipped with a source fine grid, the actual literal marked jump-measure total count over (0,T]×ℝ has ENNReal expectation precisely T times the original X.ν((−∞,0)). The proof uses an 𝓕_T-measurable proxy F identical almost everywhere to the same source count, its exact Poisson law, and converts the weighted real Poisson moment into a genuine original-source lintegral using nonnegative countable integration and original-path finite-activity support. It does not assert the distribution of negative individual marks or arbitrary-B compensation.
-- source:
--   Uses new original source natural-valued summable moment bridge, ENNReal.ofReal_tsum_of_nonneg and lintegral_tsum to establish literal N_X source expected count. Proved 8bd and 0bd are imported through bridge; no marked law assumed.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_bv_actual_source_count_nat_supported_summable_poisson_moment
open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_wave5_01_bv_actual_intrinsic_total_count_lintegral_equals_source_levy_rate
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (T : ℝ≥0) (hT : 0 < T)
    (grid : ℕ → ℕ → ℝ≥0)
    (hGrid : ∀ n : ℕ, 0 < n →
      StrictMono (grid n) ∧ grid n 0 = 0 ∧ grid n n = T)
    (hMesh : ∀ δ : ℝ, 0 < δ →
      ∀ᶠ n : ℕ in atTop, ∀ i : ℕ, i < n →
        dist (grid n i) (grid n (i + 1)) < δ)
    (hBound : ∀ n i : ℕ, i ≤ n → grid n i ≤ T) :
    (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ (Set.univ : Set ℝ)) ∂P) =
      (T : ℝ≥0∞) * X.ν (Iio (0 : ℝ)) := by sorry
