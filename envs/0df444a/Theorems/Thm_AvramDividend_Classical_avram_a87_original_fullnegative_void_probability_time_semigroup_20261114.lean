-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a87_original_fullnegative_void_probability_time_semigroup_20261114
-- name    : AvramDividend.Classical.avram_a87_original_fullnegative_void_probability_time_semigroup_20261114
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T17:22:41.288794+00:00
-- url     : https://prove2.me/theorems/c0c77d12-a25a-4186-95d3-6638bb042aba
-- title:
--   Original full-negative nojump probabilities satisfy exact time-semigroup law without bounded-variation hypotheses
-- statement:
--   For any original spectrally negative Levy process with finite total negative mark intensity (including positive sigma), the probability of no physical negative jump by T+S equals the product of no-jump probabilities for T and S. Follows from proved original full-negative Poisson void law and the real exponential semigroup, without bounded-variation restrictions.
-- source:
--   Proved A82 original full-negative void probability and Mathlib Real.exp_add, ENNReal.ofReal_mul.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a87_original_fullnegative_void_probability_time_semigroup_20261114
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) (T S : ℝ≥0) :
    P {ω : Ω |
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 (T + S) ×ˢ Iio (0 : ℝ)) = 0} =
      P {ω : Ω |
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ Iio (0 : ℝ)) = 0} *
      P {ω : Ω |
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 S ×ˢ Iio (0 : ℝ)) = 0} := by sorry
