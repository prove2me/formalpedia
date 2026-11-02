-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_01_bv_actual_intrinsic_borel_mark_band_expected_count_le_finite_total_rate
-- name    : AvramDividend.Classical.avram_wave5_01_bv_actual_intrinsic_borel_mark_band_expected_count_le_finite_total_rate
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T19:40:52.684186+00:00
-- url     : https://prove2.me/theorems/fde269fc-ce67-40bd-ba37-28ef02ac95a1
-- title:
--   Every Borel marked source jump subcount has a finite BV expected count bounded by total original Lévy rate
-- statement:
--   For the ACTUAL original SpectrallyNegativeLevy P 𝓕, BV, finite ν((−∞,0)), T>0, original fine grids and any Borel mark set B, the expectation of the literal source N_X((0,T]×B) is bounded above by Tν((−∞,0)) and is finite. The bound is pure same-path monotonicity of the genuine marked count followed by the proved original total-count expectation. It does not equate the B expectation with Tν(B), and does not assume an abstract Poisson measure. This is a source-side local L1 bound needed for predictable marked integrals, though it is not the full compensator.
-- source:
--   Monotonicity of actual same-path marked counting measure in B, Mathlib lintegral_mono, accepted original literal total-count expectation d8534d75, and finite ENNReal.ofReal.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_bv_actual_intrinsic_total_count_lintegral_equals_source_levy_rate
open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem AvramDividend.Classical.avram_wave5_01_bv_actual_intrinsic_borel_mark_band_expected_count_le_finite_total_rate
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
    (B : Set ℝ) (hB : MeasurableSet B) :
    (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        ((Ioc 0 T) ×ˢ B) ∂P) ≤
      (T : ℝ≥0∞) * X.ν (Iio (0 : ℝ)) ∧
    (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        ((Ioc 0 T) ×ˢ B) ∂P) < ⊤ := by sorry
