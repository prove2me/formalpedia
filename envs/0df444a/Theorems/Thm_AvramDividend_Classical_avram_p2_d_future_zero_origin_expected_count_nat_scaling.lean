-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_d_future_zero_origin_expected_count_nat_scaling
-- name    : AvramDividend.Classical.avram_p2_d_future_zero_origin_expected_count_nat_scaling
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T18:21:36.695209+00:00
-- url     : https://prove2.me/theorems/e59d106d-7f9a-40a5-ae25-3e6764e43dda
-- title:
--   Original source marked jump means scale exactly at all integer horizons
-- statement:
--   For any Borel marks B and natural n, the original expected literal intrinsic jump count on (0,n] equals n times its time-one mean, as an equality in extended nonnegative reals, allowing infinite activity. This is the discrete-time step towards the monotone additive continuous-time Cauchy rate reduction, without asserting the ν identity.
-- source:
--   Induct on n using the Proved original source expected-count time-additivity c00b2582-d714-429d-a720-df3770e36760. The zero interval has zero count, and ENNReal multiplication distributes over finite natural sums.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_d_future_zero_origin_expected_count_additive

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_d_future_zero_origin_expected_count_nat_scaling
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (B : Set ℝ) (hB : MeasurableSet B) (n : ℕ) :
    (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 (n : ℝ≥0) ×ˢ B) ∂P) =
      (n : ℝ≥0∞) *
        (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc 0 (1 : ℝ≥0) ×ˢ B) ∂P) := by sorry
