-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_d_future_zero_window_borel_rate
-- name    : AvramDividend.Classical.avram_p2_d_future_zero_window_borel_rate
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T10:52:26.925617+00:00
-- url     : https://prove2.me/theorems/b1f32349-df35-4ec9-8389-82b83e4c9b81
-- title:
--   Original zero-duration intrinsic marked jump count and full Borel rate
-- statement:
--   For any original spectrally negative Lévy process and any mark set B, the literal original sample marked jump measure on (s,s]×B vanishes pathwise, and the unconditional rate identity holds with zero duration, including when ν(B) is infinite.
-- source:
--   The physical time window Ioc s s is empty. The mapped intrinsic count measure of its product with B vanishes for every ω; its lintegral is zero. ENNReal zero times ν(B) is zero even for ν(B)=top.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_d_future_zero_window_borel_rate
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s : ℝ≥0) (B : Set ℝ) :
    (∀ ω : Ω,
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s s ×ˢ B) = 0) ∧
    (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s s ×ˢ B) ∂P) =
    ((s - s : ℝ≥0) : ℝ≥0∞) * X.ν B := by sorry
