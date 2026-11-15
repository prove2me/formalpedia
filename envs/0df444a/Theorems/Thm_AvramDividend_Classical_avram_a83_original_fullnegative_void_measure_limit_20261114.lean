-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a83_original_fullnegative_void_measure_limit_20261114
-- name    : AvramDividend.Classical.avram_a83_original_fullnegative_void_measure_limit_20261114
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T17:06:32.589227+00:00
-- url     : https://prove2.me/theorems/76e95143-2fa2-4e1a-83a9-d8355c5264cd
-- title:
--   Original full-negative physical nojump event probability is limit of reciprocal-band nojump probabilities
-- statement:
--   For a spectrally negative original Lévy process on the original filtered probability space, continuity of the jump counting measures and continuity of probability from above identify the full negative nojump event with the limit of shrinking-cutoff void-event probabilities, without bounded-variation or volatility assumptions.
-- source:
--   Proved b196/b197 reciprocal-band exhaustion and physical count-measure convergence, p2_e measurable rectangle counts; Mathlib finite measure continuity from above.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a83_original_fullnegative_void_measure_limit_20261114
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) :
    Tendsto (fun n : ℕ =>
      P {ω : Ω |
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc 0 T ×ˢ Iic (-(1 / ((n : ℝ) + 1)))) = 0})
      atTop (𝓝 (P {ω : Ω |
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc 0 T ×ˢ Iio (0 : ℝ)) = 0})) := by sorry
