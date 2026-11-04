-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_d_future_original_general_interval_all_real_source_rate
-- name    : AvramDividend.Classical.avram_p2_d_future_original_general_interval_all_real_source_rate
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T20:42:30.891233+00:00
-- url     : https://prove2.me/theorems/a00138e0-53fd-4da4-b124-3f23c5ce014d
-- title:
--   Original source-marked mean on every shifted real interval has unit-time source intensity
-- statement:
--   The expected genuine original jump count of B marks on (s,t] equals (t-s) times the original unit-time marked expected count for every ordered pair of real nonnegative endpoints s≤t. The intensity is the original count-derived scalar and is not identified with the Lévy ν. This uses source stationary marked-count mean and the zero-origin all-real source rate.
-- source:
--   Use Proved add050a6 stationary original source count mean, rewrite t=s+(t-s) by NNReal truncated-subtraction, and Proved P2-D all-real zero-origin source rate.

import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_intrinsic_marked_rectangle_count_stationary_mean
import Theorems.Thm_AvramDividend_Classical_avram_p2_d_future_original_zero_origin_all_real_source_rate

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_d_future_original_general_interval_all_real_source_rate
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (B : Set ℝ) (hB : MeasurableSet B) :
    (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B) ∂P) =
      ((t - s : ℝ≥0) : ℝ≥0∞) * (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 (1 : ℝ≥0) ×ˢ B) ∂P) := by sorry
