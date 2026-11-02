-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_01_bv_original_future_negative_mark_interval_exact_rate
-- name    : AvramDividend.Classical.avram_wave6_01_bv_original_future_negative_mark_interval_exact_rate
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T22:07:06.009231+00:00
-- url     : https://prove2.me/theorems/c7a926f3-2b09-4614-ae82-f607fc1a0058
-- title:
--   Original finite-BV strictly negative genuine future jump marks have exact time-gap Lévy mean
-- statement:
--   For actual original BV finite-activity X and 0<s≤t, the expected number of actual strictly negative Lévy jumps in the physical interval (s,t] equals (t-s)·X.ν((−∞,0)). The proof uses pointwise source spectral support to identify the negative-mark count with the full-mark count and the already Proved original future total-rate identity. This is a genuine positive-intensity marked B=(−∞,0) instance, not arbitrary B and not a Poisson-copy law.
-- source:
--   Proved original intrinsic measure negative-support 12e84fff and exact fullmark future interval rate e16568b7; measure_union and real-line split Iio0 ∪ Ici0.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_01_bv_original_future_fullmark_expected_count_exact_gap_rate
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_intrinsic_jump_measure_negative_support
open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave6_01_bv_original_future_negative_mark_interval_exact_rate
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
      (Ioc s t ×ˢ Iio (0 : ℝ)) ∂P) =
      ((t - s : ℝ≥0) : ℝ≥0∞) * X.ν (Iio (0 : ℝ)) := by sorry
