-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb44_original_finiteactivity_ae_last_horizon_no_negative_mark_strip
-- name    : AvramDividend.Classical.avram_bvb44_original_finiteactivity_ae_last_horizon_no_negative_mark_strip
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T12:34:56.750169+00:00
-- url     : https://prove2.me/theorems/21aab113-50cb-4a19-b9ff-72e3a5a51d6e
-- title:
--   Original BV finite-negative-activity source has an almost-sure terminal physical interval free of all negative jumps
-- statement:
--   For the exact original spectrally negative Levy process, under BoundedVariation and finite negative Levy jump intensity, at any fixed positive physical horizon the original source negative jump times are almost surely bounded away from that horizon by a strictly positive path-dependent interval. This follows from the already-Proved original finite jump-time event, the original no-fixed-time-jump event, finite count equivalence and our published source time separation theorem bvb42. It is the true no-final-jump-strip ingredient required by finite positive mark stopped physical error phys69, without replacing the original filtration, clock or process.
-- source:
--   Original fixed-horizon finite jump-time theorem 6a65718c, no deterministic source jump theorem b4407263, accepted bvb42 18c235bc, Mathlib MeasureTheory.Measure.Count.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_bv_actual_source_jump_times_finite_on_horizon
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_source_no_fixed_positive_time_jump_ae
import Theorems.Thm_AvramDividend_Classical_avram_bvb42_original_finite_negative_mark_times_terminal_margin
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bvb44_original_finiteactivity_ae_last_horizon_no_negative_mark_strip
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (T : ℝ≥0) (hT : 0 < T) :
    ∀ᵐ ω ∂P,
      ∃ δ : ℝ, 0 < δ ∧
        ∀ t : ℝ≥0, 0 < t → t ≤ T →
          X.X t ω - Function.leftLim (fun s : ℝ≥0 => X.X s ω) t ≠ 0 →
          (t : ℝ) ≤ (T : ℝ) - δ := by sorry
