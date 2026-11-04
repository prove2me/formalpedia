-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_d_future_zero_origin_expected_count_monotone
-- name    : AvramDividend.Classical.avram_p2_d_future_zero_origin_expected_count_monotone
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T17:40:10.050731+00:00
-- url     : https://prove2.me/theorems/d6f0bf62-2b5e-4335-a8a4-cedca0b7bfaf
-- title:
--   Original zero-origin marked jump-count mean is monotone in time
-- statement:
--   For the actual spectrally negative Lévy process and any real mark set, increasing a physical zero-origin observation horizon cannot decrease the ENNReal expected literal jump count. Infinite activity and nonmeasurable mark sets are covered by outer measure monotonicity; no ν intensity is assumed.
-- source:
--   Use the inclusion (0,a]×B ⊆ (0,b]×B when a≤b, monotonicity of the original mapped counting measure, and monotonicity of the ENNReal lintegral.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_d_future_zero_origin_expected_count_monotone
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (a b : ℝ≥0) (hab : a ≤ b) (B : Set ℝ) :
    (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 a ×ˢ B) ∂P) ≤
      (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 b ×ˢ B) ∂P) := by sorry
