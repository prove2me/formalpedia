-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_root29_05_shifted_future_raw_ruin_eq_strict_drawdown_subtype_clock
-- name    : AvramDividend.Classical.avram_root29_05_shifted_future_raw_ruin_eq_strict_drawdown_subtype_clock
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T15:53:25.635168+00:00
-- url     : https://prove2.me/theorems/04cbe892-11e6-4e4b-9706-6091d9c7fe36
-- title:
--   Exact shifted future barrier ruin clock equals strict drawdown subtype clock
-- statement:
--   On each original Lévy path at every finite shifted age, the exact future ruin clock appearing in dividendValue_barrierStrategy_expected_futureRuin_stoppedReward equals the first strict future-increment drawdown below -a, with no change of strictness or endpoint.
-- source:
--   Use the remotely Proved source-specific shiftedLevy_ruin_threshold_iff_increment_runningSup, elementary linear arithmetic, and Lean iInf_subtype conversion. This is needed to substitute the genuine sampled drawdown clock after first upcrossing.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_shiftedLevy_ruin_threshold_iff_increment_runningSup

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal Classical

/-- The exact future ruin clock used by the true barrier dividend
Stieltjes formula equals strict drawdown of the shifted increment record. -/

theorem AvramDividend.Classical.avram_root29_05_shifted_future_raw_ruin_eq_strict_drawdown_subtype_clock
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (age : ℝ≥0) (a : ℝ) :
    (⨅ (r : ℝ≥0)
      (_ : a + (X.X (age + r) ω - X.X age ω) <
        max 0
          (sSup ((fun z : ℝ≥0 => X.X (age + z) ω) '' Icc 0 r) -
            X.X age ω)), (r : ℝ≥0∞)) =
    (⨅ i : {r : ℝ≥0 //
       (X.X (age + r) ω - X.X age ω) -
       sSup ((fun z : ℝ≥0 => X.X (age + z) ω - X.X age ω) ''
         Icc 0 r) < -a}, (i.1 : ℝ≥0∞)) := by sorry
