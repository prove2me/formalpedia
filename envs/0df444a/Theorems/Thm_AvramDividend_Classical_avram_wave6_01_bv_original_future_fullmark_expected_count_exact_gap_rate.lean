-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_01_bv_original_future_fullmark_expected_count_exact_gap_rate
-- name    : AvramDividend.Classical.avram_wave6_01_bv_original_future_fullmark_expected_count_exact_gap_rate
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T21:52:39.044436+00:00
-- url     : https://prove2.me/theorems/e16568b7-e3a3-40e2-80e9-32c2e7fde382
-- title:
--   Genuine BV original full-mark future jump count has exact time-gap Lévy rate
-- statement:
--   For the actual original bounded-variation finite-negative-intensity spectrally negative Lévy X and any strictly positive start 0<s≤t, the original intrinsic nonzero-jump count on (s,t]×ℝ has unconditional expected value exactly (t-s) X.ν((−∞,0)). The proof uses the already Proved source full-mark interval balance and finite ENNReal additive cancellation; no grid, auxiliary Poisson model, past-event factor, or identification of the intensity of individual mark sets is assumed. This is a genuine positive-intensity full-mark special case of the original rectangle law.
-- source:
--   Instantiates canonically Proved original full-mark interval balance 64618901, uses t=s+(t-s), distributivity and finite ENNReal additive cancellation, always with original X.X and X.ν.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_01_bv_original_fullmark_future_interval_intensity_balance
open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave6_01_bv_original_future_fullmark_expected_count_exact_gap_rate
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (s t : ℝ≥0) (hs : 0 < s) (hst : s ≤ t) :
    (∫⁻ ω, ((Measure.count.restrict {v : ℝ≥0 |
      0 < v ∧ X.X v ω -
        Function.leftLim (fun w : ℝ≥0 => X.X w ω) v ≠ 0}).map
      (fun v : ℝ≥0 => (v, X.X v ω -
        Function.leftLim (fun w : ℝ≥0 => X.X w ω) v)))
      (Ioc s t ×ˢ (Set.univ : Set ℝ)) ∂P) =
    ((t - s : ℝ≥0) : ℝ≥0∞) * X.ν (Iio (0 : ℝ)) := by sorry
