-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_19_original_finite_horizon_clock_strict_stabilises
-- name    : AvramDividend.Classical.avram_wave7_19_original_finite_horizon_clock_strict_stabilises
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T13:57:46.497175+00:00
-- url     : https://prove2.me/theorems/62753faa-b3c6-4a84-ab5d-7379f6fceb89
-- title:
--   Exact original ruin-payment domain stabilises under any clock strictly beyond the finite horizon
-- statement:
--   For original SpectrallyNegativeLevy X and its actual ruinTime, any integer clock whose ENNReal value strictly exceeds the finite nonnegative horizon T gives exactly the same paymentTimes domain through T as the untruncated ruin clock, for every path and every ruin state. The right dividend at t=0 remains admissible even if ruinTime=0; positive ruin-time right payments remain excluded. Hence the original discounted Stieltjes cash is pathwise identical at these two domains, with no Fatou or uniform integrability requirement. No process regularity or strategy hypothesis is used.
-- source:
--   Source-specific original ruinTime and paymentTimes; W7-08 finite positive n budget d457be6b-c74a-4a7e-aea2-4bb6222642d5; W7-11 uniform clock bridge e43bdc5f-627b-4e07-80b1-5c34e8662cbe.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_19_original_finite_horizon_clock_strict_stabilises
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (T : ℝ) (hT : 0 ≤ T) (n : ℕ)
    (hn : ENNReal.ofReal T < (n : ℝ≥0∞)) :
    paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)) ∩ Iic T =
      paymentTimes (ruinTime X x D ω) ∩ Iic T := by sorry
