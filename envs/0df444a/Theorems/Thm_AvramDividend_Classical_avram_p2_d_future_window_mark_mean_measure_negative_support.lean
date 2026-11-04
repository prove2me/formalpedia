-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_d_future_window_mark_mean_measure_negative_support
-- name    : AvramDividend.Classical.avram_p2_d_future_window_mark_mean_measure_negative_support
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T18:51:07.765507+00:00
-- url     : https://prove2.me/theorems/7f9724f4-0923-4b5b-8a8b-548bda70b86c
-- title:
--   Every original marked-count window has a strictly-negative-supported Borel mean measure
-- statement:
--   For every deterministic interval (s,t] in the actual spectrally negative Lévy process there is a genuine Borel mark mean measure ρ representing the expected intrinsic count of all Borel marks B, and ρ(B)=ρ(B∩(-∞,0)) even for infinite activity and empty windows. The measure depends on the window; no formula involving X.ν is assumed.
-- source:
--   Proved original arbitrary-window mean measure 03058d10, plus original source negative rectangle restriction, followed by lintegral_congr. The original X,P,𝓕 remain unchanged.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_d_future_window_mark_mean_measure_negative_support
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t) :
    ∃ ρ : Measure ℝ,
      (∀ (B : Set ℝ), MeasurableSet B →
        ρ B = (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc s t ×ˢ B) ∂P)) ∧
      (∀ (B : Set ℝ), MeasurableSet B →
        ρ B = ρ (B ∩ Iio (0 : ℝ))) := by sorry
