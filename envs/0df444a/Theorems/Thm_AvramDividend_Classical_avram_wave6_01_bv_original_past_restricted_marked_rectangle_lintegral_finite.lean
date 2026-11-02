-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_01_bv_original_past_restricted_marked_rectangle_lintegral_finite
-- name    : AvramDividend.Classical.avram_wave6_01_bv_original_past_restricted_marked_rectangle_lintegral_finite
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T19:48:03.747525+00:00
-- url     : https://prove2.me/theorems/c35d0d44-cbdd-482f-9b63-230a50a44794
-- title:
--   Original BV finite-activity past-restricted marked jump rectangles have uniformly finite first moments
-- statement:
--   For the original spectrally negative Levy process on its unchanged sample space and filtration, under BV and finite total activity with an actual deterministic fine-grid system, every genuine original-path marked jump-count integral over an F_s-event and (s,T] is finite and bounded by T times X.ν((−∞,0)). The bound uses the canonically proved literal original source count first moment and monotonicity of the intrinsic measure and integral. It supplies honest ENNReal L1 bookkeeping for the predictable rectangle proof without presupposing ν(B) as its intensity.
-- source:
--   Direct corollary of canonically Proved fde269fc-ce67-40bd-ba37-28ef02ac95a1, with same-path time inclusion, measure_mono, measurable past indicator and lintegral_mono. No Poisson replacement or ν(B) identity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_bv_actual_intrinsic_borel_mark_band_expected_count_le_finite_total_rate

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave6_01_bv_original_past_restricted_marked_rectangle_lintegral_finite
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
    (s : ℝ≥0) (hst : s ≤ T)
    (A : Set Ω) (hA : MeasurableSet[𝓕 s] A)
    (B : Set ℝ) (hB : MeasurableSet B) :
    (∫⁻ ω in A, ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω - Function.leftLim
        (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω - Function.leftLim
          (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s T ×ˢ B) ∂P) ≤
      (T : ℝ≥0∞) * X.ν (Iio (0 : ℝ)) ∧
    (∫⁻ ω in A, ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω - Function.leftLim
        (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω - Function.leftLim
          (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s T ×ˢ B) ∂P) < ⊤ := by sorry
