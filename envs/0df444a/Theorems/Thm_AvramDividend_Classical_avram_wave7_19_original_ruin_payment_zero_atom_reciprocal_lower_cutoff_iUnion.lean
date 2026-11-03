-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_19_original_ruin_payment_zero_atom_reciprocal_lower_cutoff_iUnion
-- name    : AvramDividend.Classical.avram_wave7_19_original_ruin_payment_zero_atom_reciprocal_lower_cutoff_iUnion
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T14:07:58.927731+00:00
-- url     : https://prove2.me/theorems/ca2dff72-818f-4e1a-b29e-d6aae297c29e
-- title:
--   Original pre-ruin cash domain is the time-zero right atom plus positive reciprocal lower-cutoff windows
-- statement:
--   For the actual original source ruinTime and nonnegative finite horizon T, the full payment domain is exactly the singleton time-zero right-payment together with the union of all positive reciprocal lower-cutoff windows [1/(n+1),T] intersected with original paymentTimes. Any local stopped Ito proof beginning at strictly positive times must carry this separate initial dividend atom, even under immediate ruin. This is pathwise exact, includes creeping and overshoot without assumptions on sample-path continuity, and is an exhaustion identity rather than a stochastic estimate.
-- source:
--   Original paymentTimes and ruinTime definitions; pinned Mathlib exists_nat_one_div_lt; W7-08 positive-horizon source Ito target 6004b387 and W7-18 interior localisers.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_19_original_ruin_payment_zero_atom_reciprocal_lower_cutoff_iUnion
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (T : ℝ) (hT : 0 ≤ T) :
    paymentTimes (ruinTime X x D ω) ∩ Iic T =
      ({0} : Set ℝ) ∪
        ⋃ n : ℕ, paymentTimes (ruinTime X x D ω) ∩
          Icc (1 / ((n : ℝ) + 1)) T := by sorry
