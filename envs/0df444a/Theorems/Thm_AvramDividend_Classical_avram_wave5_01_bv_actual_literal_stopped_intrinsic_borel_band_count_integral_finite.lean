-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_01_bv_actual_literal_stopped_intrinsic_borel_band_count_integral_finite
-- name    : AvramDividend.Classical.avram_wave5_01_bv_actual_literal_stopped_intrinsic_borel_band_count_integral_finite
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T19:45:39.991324+00:00
-- url     : https://prove2.me/theorems/501d070f-4350-4d87-bd10-bbf6256a97a4
-- title:
--   Literal original BV stopped source marked count has finite expectation under any source random clock
-- statement:
--   For genuine original SpectrallyNegativeLevy P 𝓕, BV, finite negative Lévy rate, T>0 and source fine-grid hypotheses, every sample clock τ:Ω→ENNReal (hence every original-filtration stopping time) and every Borel mark band B give a literal original jump count restricted to times 0<u≤T with u≤τ(ω), whose expected count is ≤Tν((−∞,0))<∞. The proof uses only the same-path set inclusion into the full source count and the proved original literal total expected count. The bound is uniform in τ and B; no abstract Poisson process, mark-intensity equality, adaptedness assumption or future compensator is invented.
-- source:
--   Direct measure_mono each original ω and lintegral_mono followed by d8534d75. Finite rate follows from νnegative<∞ and T finite.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_bv_actual_intrinsic_total_count_lintegral_equals_source_levy_rate
open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem AvramDividend.Classical.avram_wave5_01_bv_actual_literal_stopped_intrinsic_borel_band_count_integral_finite
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
    (hBound : ∀ n i : ℕ, i ≤ n → grid n i ≤ T)
    (τ : Ω → ℝ≥0∞)
    (B : Set ℝ) (hB : MeasurableSet B) :
    (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        ({u : ℝ≥0 | u ∈ Ioc 0 T ∧ (u : ℝ≥0∞) ≤ τ ω} ×ˢ B) ∂P) ≤
      (T : ℝ≥0∞) * X.ν (Iio (0 : ℝ)) ∧
    (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        ({u : ℝ≥0 | u ∈ Ioc 0 T ∧ (u : ℝ≥0∞) ≤ τ ω} ×ˢ B) ∂P) < ⊤ := by sorry
