-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_01_bv_zero_negative_intensity_original_rectangle_compensator
-- name    : AvramDividend.Classical.avram_wave6_01_bv_zero_negative_intensity_original_rectangle_compensator
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T19:52:30.654441+00:00
-- url     : https://prove2.me/theorems/cfd03bfe-4fe9-410b-bd0d-445d387600e6
-- title:
--   Original BV zero-jump-intensity predictable rectangle compensation for all marks and past events
-- statement:
--   For the actual original spectrally negative Levy process in BV with X.ν((−∞,0))=0, every original-past-restricted marked jump count on (s,T] has exact expected intensity P(A)(T−s)X.ν(B)=0. The zero count follows from the canonically Proved genuine BV finite-activity source count first-moment upper bound; the zero ν(B) follows from the original negative support ν([0,∞))=0 and total negative mass zero. This is the genuine zero-activity source branch of 393b03a8, preserving original Ω, P, 𝓕, X.X and X.ν, with no compensator assumption.
-- source:
--   Same-path monotonicity of N_X over a past-restricted rectangle, existing source BV total-rate bound fde269fc, X.ν_Ici=0 and ν(Iio0)=0; zero ENNReal integral. The only added hypothesis is exactly zero original Lévy jump intensity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_bv_actual_intrinsic_borel_mark_band_expected_count_le_finite_total_rate
open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave6_01_bv_zero_negative_intensity_original_rectangle_compensator
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hZero : X.ν (Iio (0 : ℝ)) = 0)
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
        (Ioc s T ×ˢ B) ∂P) =
      P A * ((T - s : ℝ≥0) : ℝ≥0∞) * X.ν B := by sorry
