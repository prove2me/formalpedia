-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_d_future_negative_unit_mean_to_arbitrary_borel_rate
-- name    : AvramDividend.Classical.avram_p2_d_future_negative_unit_mean_to_arbitrary_borel_rate
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T21:18:56.196548+00:00
-- url     : https://prove2.me/theorems/af526de8-1f0a-43f4-9232-ada798016437
-- title:
--   Negative original unit-mark ν identification suffices for all real intervals and arbitrary Borel marks
-- statement:
--   An explicit conditional reduction: identifying the expected original unit-time marked count with X.ν(C) only for negative Borel marks C suffices for the exact original arbitrary-time arbitrary-Borel unconditional Lévy rate. Real-time linearity and negative support are already proved. This does not establish or assume the outstanding identification in the canonical theorem.
-- source:
--   Combine Proved original all-real source rate a00138e0 and Proved arbitrary-mark support reduction 9d64d756. No Poisson copy or additional independent process.

import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_d_future_original_general_interval_all_real_source_rate
import Theorems.Thm_AvramDividend_Classical_avram_p2_d_future_arbitrary_borel_rate_of_negative_rate

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_d_future_negative_unit_mean_to_arbitrary_borel_rate
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (B : Set ℝ) (hB : MeasurableSet B)
    (hunitNegative : ∀ (C : Set ℝ), MeasurableSet C →
      C ⊆ Iio (0 : ℝ) → (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 (1 : ℝ≥0) ×ˢ C) ∂P) = X.ν C) :
    (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B) ∂P) = ((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B := by sorry
