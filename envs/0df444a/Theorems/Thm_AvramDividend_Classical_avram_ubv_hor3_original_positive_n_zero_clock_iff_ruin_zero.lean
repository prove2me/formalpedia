-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_hor3_original_positive_n_zero_clock_iff_ruin_zero
-- name    : AvramDividend.Classical.avram_ubv_hor3_original_positive_n_zero_clock_iff_ruin_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T13:23:11.475533+00:00
-- url     : https://prove2.me/theorems/29044b53-675b-4f1b-afee-1d5b5918ae70
-- title:
--   Original positive integer clipped natural ruin clock vanishes exactly on immediate ruin
-- statement:
--   For an actual original controlled spectrally negative Lévy process and any strictly positive integer clock n, the extended-nonnegative truncated ruin stopping clock min(ruinTime X x D ω,n) equals zero exactly when the original ruinTime is zero. This identifies the stopped-time-zero boundary used in localisation without loss of the genuine dividend process.
-- source:
--   Pinned Mathlib ENNReal.min_eq_zero_iff and strict positivity of natural n cast to ENNReal; no stochastic process equality-in-law or downstream canonical theorem.

import Mathlib.Data.ENNReal.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_hor3_original_positive_n_zero_clock_iff_ruin_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (n : ℕ) (hn : 0 < n) (ω : Ω) :
    (min (ruinTime X x D ω) (n : ℝ≥0∞) = 0) ↔
      (ruinTime X x D ω = 0) := by sorry
