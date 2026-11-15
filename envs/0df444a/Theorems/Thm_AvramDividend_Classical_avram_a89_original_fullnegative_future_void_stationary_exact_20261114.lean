-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a89_original_fullnegative_future_void_stationary_exact_20261114
-- name    : AvramDividend.Classical.avram_a89_original_fullnegative_future_void_stationary_exact_20261114
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T18:16:02.331547+00:00
-- url     : https://prove2.me/theorems/f143c2e6-6f0e-4977-8935-29338ba931bb
-- title:
--   Finite-negative-activity Lévy process: original shifted nojump probability has exact stationary Poisson intensity
-- statement:
--   For every original spectrally negative Lévy process with finite negative Lévy jump mass, the probability of no physical negative jump on (s,s+T] is exp(-T times the full negative Lévy mass), independently of s, even when Gaussian variance is positive.
-- source:
--   Proved p4_s3_interval_h original physical marked count stationary measure.map law; Proved p2_e marked count measurability; Proved A82 original full-negative zero-count Poisson probability.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a89_original_fullnegative_future_void_stationary_exact_20261114
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (s T : ℝ≥0) :
    P {ω : Ω |
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s (s + T) ×ˢ Iio (0 : ℝ)) = 0} =
      ENNReal.ofReal (Real.exp
        (-((T : ℝ) * (X.ν (Iio (0 : ℝ))).toReal))) := by sorry
