-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_d_future_expected_count_integer_horizon_bound
-- name    : AvramDividend.Classical.avram_p2_d_future_expected_count_integer_horizon_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T18:56:10.1762+00:00
-- url     : https://prove2.me/theorems/98eca88c-b128-4d3f-8561-62cf92f4fe73
-- title:
--   Original bounded-horizon marked expectation controlled by an integer unit-time mean multiple
-- statement:
--   For the original spectrally negative Lévy process, any Borel mark set B, and physical time t≤n with n a natural number, the expected intrinsic jump count over (0,t] is at most n times the original first-unit expected marked count, in ENNReal. No ν-rate or local finiteness is imposed.
-- source:
--   Combines Proved original zero-origin mean monotonicity d6f0bf62 with Proved original integer unit scaling e59d106d. This provides a source-faithful finite-window expectation envelope relevant to localization and UI.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_d_future_expected_count_integer_horizon_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (B : Set ℝ) (hB : MeasurableSet B)
    (t : ℝ≥0) (n : ℕ) (ht : t ≤ (n : ℝ≥0)) :
    (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 t ×ˢ B) ∂P) ≤ (n : ℝ≥0∞) * (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 (1 : ℝ≥0) ×ˢ B) ∂P) := by sorry
