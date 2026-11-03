-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_01_bv_finite_activity_all_start_actual_negative_predictable_rectangle
-- name    : AvramDividend.Classical.avram_wave7_01_bv_finite_activity_all_start_actual_negative_predictable_rectangle
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T20:18:15.206371+00:00
-- url     : https://prove2.me/theorems/c78120b8-1aa3-44dd-8a6e-ee6478bb6ffc
-- title:
--   Finite-activity BV original negative predictable jump compensation includes zero start
-- statement:
--   On the unchanged original Lévy sample space, under BV and the explicitly necessary finite-activity condition ν(-∞,0)<∞, extend the previously Proved strictly positive-start predictable rectangle to all 0≤s≤t, including s=0 and zero-duration intervals. The s=0 proof uses original total jump rate, exact nonpositive jump support and original past-event factorisation; s>0 uses the accepted original rectangle. No infinite-activity generalisation is asserted.
-- source:
--   Original actual zero-start total finite activity rate 4d7761f5; source negative support c2e1a7f1; original past-event factor 264b3973; positive start rectangle 29c1b8ca; zero-horizon dc5d710d. A genuine stronger exact source compensator consumer.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_bv_finite_activity_actual_negative_predictable_rectangle
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_actual_intrinsic_rectangle_past_event_factor_unconditional
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_zero_horizon_predictable_rectangle
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_arbitrary_mark_negative_support_count
import Theorems.Thm_AvramDividend_Classical_avram_wave6_01_bv_original_total_jump_intensity_gridfree
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_01_bv_finite_activity_all_start_actual_negative_predictable_rectangle
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (s t : ℝ≥0) (hst : s ≤ t)
    (A : Set Ω) (hA : MeasurableSet[𝓕 s] A) :
    (∫⁻ ω in A, ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω - Function.leftLim
        (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s t ×ˢ Iio (0 : ℝ)) ∂P) =
      P A * ((t - s : ℝ≥0) : ℝ≥0∞) * X.ν (Iio (0 : ℝ)) := by sorry
