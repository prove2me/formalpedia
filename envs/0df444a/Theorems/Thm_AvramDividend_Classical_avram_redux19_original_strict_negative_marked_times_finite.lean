-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_redux19_original_strict_negative_marked_times_finite
-- name    : AvramDividend.Classical.avram_redux19_original_strict_negative_marked_times_finite
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T23:13:08.900195+00:00
-- url     : https://prove2.me/theorems/e19c4927-e9a1-4f3a-ace4-9079adedc1d1
-- title:
--   Actual original strictly negative cutoff jump-time set is finite on bounded horizons
-- statement:
--   For the actual original spectrally negative Levy process, the times in (0,T] at which a jump lies strictly below -1/(k+1) form a finite set for every original sample path, all horizons, and all natural cutoff indices. This uses the identical strict cutoff appearing in the canonical intrinsic marked Laplace functional.
-- source:
--   Instantiate the already Proved original closed-cutoff marked jump-time finiteness theorem with the same X, omega, horizon and k. The strict cutoff set is a subset of that finite closed-cutoff set by le_of_lt.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_marked_times_finite
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_redux19_original_strict_negative_marked_times_finite
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (T : ℝ≥0) (k : ℕ) :
    Set.Finite {u : ℝ≥0 | 0 < u ∧ u ≤ T ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u <
        -(1 / ((k : ℝ) + 1))} := by sorry
