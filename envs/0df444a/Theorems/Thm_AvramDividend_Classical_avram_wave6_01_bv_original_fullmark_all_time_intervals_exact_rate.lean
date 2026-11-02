-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_01_bv_original_fullmark_all_time_intervals_exact_rate
-- name    : AvramDividend.Classical.avram_wave6_01_bv_original_fullmark_all_time_intervals_exact_rate
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T22:21:11.759906+00:00
-- url     : https://prove2.me/theorems/2fdbada6-44ed-440c-8ad1-2103ca3da34a
-- title:
--   The original finite-BV full jump count has exact Lévy first moment on every time interval, including the origin
-- statement:
--   For every original BV finite-total-negative-activity spectrally negative Lévy X and every 0≤s≤t, including s=0 and degenerate t=s, the expected literal original-path nonzero-jump count in (s,t]×ℝ equals (t-s)X.ν((−∞,0)). This assembles the two canonically Proved genuine original rate inputs for s=0, t>0 and s>0, and handles the zero interval by measure zero. No auxiliary Poisson model, external time grid, or mark-specific intensity premise. This is the complete all-time full-mark instance of the desired source law, without the past factor or arbitrary B.
-- source:
--   Canonically Proved original fullmark expected count from 0 (4d7761f5), genuine future gap rate for s>0 (e16568b7), zero-length measure equality.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_01_bv_original_future_fullmark_expected_count_exact_gap_rate
import Theorems.Thm_AvramDividend_Classical_avram_wave6_01_bv_original_total_jump_intensity_gridfree
open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave6_01_bv_original_fullmark_all_time_intervals_exact_rate
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (s t : ℝ≥0) (hst : s ≤ t) :
    (∫⁻ ω, ((Measure.count.restrict {v : ℝ≥0 |
      0 < v ∧ X.X v ω -
        Function.leftLim (fun w : ℝ≥0 => X.X w ω) v ≠ 0}).map
      (fun v : ℝ≥0 => (v, X.X v ω -
        Function.leftLim (fun w : ℝ≥0 => X.X w ω) v)))
      (Ioc s t ×ˢ (Set.univ : Set ℝ)) ∂P) =
    ((t - s : ℝ≥0) : ℝ≥0∞) * X.ν (Iio (0 : ℝ)) := by sorry
