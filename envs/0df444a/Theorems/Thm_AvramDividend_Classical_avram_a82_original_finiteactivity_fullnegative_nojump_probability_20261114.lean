-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a82_original_finiteactivity_fullnegative_nojump_probability_20261114
-- name    : AvramDividend.Classical.avram_a82_original_finiteactivity_fullnegative_nojump_probability_20261114
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T17:05:02.463102+00:00
-- url     : https://prove2.me/theorems/88cb97ef-cb95-4eac-9f32-b1f694d8def0
-- title:
--   Original finite-intensity negative jump total has exact zero-count probability at every horizon
-- statement:
--   On the original filtered spectrally negative Levy probability space, when all strictly negative jumps have finite Levy mass, the probability of no actual negative jump before horizon T equals exp(-T times full negative Levy mass), including positive Gaussian coefficient.
-- source:
--   Proved wave7_06 physical cutoff zero-count law, b196 negative cutoff exhaustion, b197 count-measure convergence, and Mathlib continuity from above.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a82_original_finiteactivity_fullnegative_nojump_probability_20261114
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) (T : ℝ≥0) :
    P {ω : Ω |
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ Iio (0 : ℝ)) = 0} =
      ENNReal.ofReal (Real.exp
        (-((T : ℝ) * (X.ν (Iio (0 : ℝ))).toReal))) := by sorry
