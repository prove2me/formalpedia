-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_d_future_zero_origin_expected_count_nat_multiple
-- name    : AvramDividend.Classical.avram_p2_d_future_zero_origin_expected_count_nat_multiple
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T18:23:12.979355+00:00
-- url     : https://prove2.me/theorems/aeac15b4-1666-4922-a670-02c1339c047f
-- title:
--   Original source expected jump counts scale by all natural multiples of any horizon
-- statement:
--   For every original source spectrally negative Lévy process, every Borel mark set, natural n and nonnegative time t, the expected intrinsic jump count on (0,n t] is n times the expectation on (0,t]. All equalities are in ENNReal and remain valid for infinite activity.
-- source:
--   Induct on n using the Proved original source expected-count additive theorem c00b2582 and semiring distributivity of natural casts. The generic n t scaling makes the denominator-clearing step for rational-time Cauchy scaling explicit.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_d_future_zero_origin_expected_count_additive

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_d_future_zero_origin_expected_count_nat_multiple
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (B : Set ℝ) (hB : MeasurableSet B)
    (t : ℝ≥0) (n : ℕ) :
    (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) (Ioc 0 ((n : ℝ≥0) * t) ×ˢ B) ∂P) =
      (n : ℝ≥0∞) * (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) (Ioc 0 t ×ˢ B) ∂P) := by sorry
