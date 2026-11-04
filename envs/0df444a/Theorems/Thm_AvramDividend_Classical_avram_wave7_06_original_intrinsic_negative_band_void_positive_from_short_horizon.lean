-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_intrinsic_negative_band_void_positive_from_short_horizon
-- name    : AvramDividend.Classical.avram_wave7_06_original_intrinsic_negative_band_void_positive_from_short_horizon
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T08:55:08.861833+00:00
-- url     : https://prove2.me/theorems/b19214cf-a13c-4252-bb86-1f896fa67c5d
-- title:
--   Original negative-band void probability positivity transfers from a subdivided horizon
-- statement:
--   For the genuine original intrinsic X negative-band count, if the source probability of no jump on a smaller interval T/(k+1) is positive, then the zero-count probability on the full T interval is positive. Uses accepted original semigroup natural-multiple power. This eliminates a possible zero-rate singularity when passing from the void semigroup to its logarithmic rate.
-- source:
--   W7-06 original semigroup positivity interface before the small-time jump intensity identification.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_06_original_intrinsic_negative_band_void_positive_from_short_horizon
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (n k : ℕ) :
    (let p : ℝ≥0 → ENNReal := fun s =>
      P {ω : Ω |
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc 0 s ×ˢ Iic (-(1 / ((n : ℝ) + 1)))) = 0}
     0 < (p (T / ((k + 1 : ℕ) : ℝ≥0))).toReal →
       0 < (p T).toReal) := by sorry
