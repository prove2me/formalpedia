-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_d_future_zero_origin_expected_count_rational_relation
-- name    : AvramDividend.Classical.avram_p2_d_future_zero_origin_expected_count_rational_relation
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T18:29:10.227197+00:00
-- url     : https://prove2.me/theorems/2786c7d2-72bf-4a14-880e-4b0c9712feb3
-- title:
--   Original expected marked counts obey rational-time scaling under denominator relations
-- statement:
--   For natural n and positive natural d, every nonnegative time t with d*t=n has expected original intrinsic marked jump count M_B(t) equal to (n/d)*M_B(1), in the extended nonnegative reals, including infinity. No identification with the Lévy ν is assumed.
-- source:
--   Use the Proved original expected-count n-fold scaling for arbitrary horizons and unit-time integer scaling, then cancel a finite positive natural denominator in ENNReal via ENNReal.mul_inv_cancel. These two original-source helpers are currently in guarded remote proof verification and must be Proved before this child proof can be submitted.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_d_future_zero_origin_expected_count_rational_relation
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (B : Set ℝ) (hB : MeasurableSet B)
    (t : ℝ≥0) (n d : ℕ) (hd : 0 < d)
    (hrel : (d : ℝ≥0) * t = (n : ℝ≥0)) :
    (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 t ×ˢ B) ∂P) =
      ((n : ℝ≥0∞) / (d : ℝ≥0∞)) * (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 (1 : ℝ≥0) ×ˢ B) ∂P) := by sorry
