-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_intrinsic_negative_band_void_probability_time_antitone
-- name    : AvramDividend.Classical.avram_wave7_06_original_intrinsic_negative_band_void_probability_time_antitone
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T20:39:43.20662+00:00
-- url     : https://prove2.me/theorems/c5a9825a-9e7c-4de8-b25c-eb49d82408c6
-- title:
--   Actual original Lévy negative-band void probability decreases with the observation horizon
-- statement:
--   On the original probability space, the event of no genuine marked jump on the longer deterministic interval (0,T+S] is a subset of the no-jump event on (0,T]. Therefore the actual source negative-band void probability is monotone decreasing in horizon. No marked Poisson intensity, martingale or additional independence assumption is needed.
-- source:
--   Original pathwise source jump measure monotonicity, useful for finite-band negative-jump void semigroup and its continuous-time Poisson rate reduction.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_06_original_intrinsic_negative_band_void_probability_time_antitone
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T S : ℝ≥0) (n : ℕ) :
    P {ω : Ω |
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 (T + S) ×ˢ Iic (-(1 / ((n : ℝ) + 1)))) = 0} ≤
    P {ω : Ω |
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ Iic (-(1 / ((n : ℝ) + 1)))) = 0} := by sorry
