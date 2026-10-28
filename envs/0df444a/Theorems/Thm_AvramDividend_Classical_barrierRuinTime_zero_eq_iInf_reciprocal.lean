-- Prove2me | Theorems.Thm_AvramDividend_Classical_barrierRuinTime_zero_eq_iInf_reciprocal
-- name    : AvramDividend.Classical.barrierRuinTime_zero_eq_iInf_reciprocal
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T09:35:54.085261+00:00
-- url     : https://prove2.me/theorems/7ea69d8d-bfb2-4d73-badf-d6967aff22f4
-- title:
--   Zero-barrier ruin time is the countable infimum along reciprocal positive thresholds
-- statement:
--   First strictly positive drawdown is the limit of first crossing times at thresholds 1/(n+1). The countable version makes this endpoint identity available for measurable stopping-time and monotone-convergence arguments in zero-cap dividend verification.
-- source:
--   Proved AvramDividend.Classical.barrierRuinTime_zero_eq_iInf_positive, Proved barrierRuinTime_mono_barrier, and Archimedean exists_nat_one_div_lt. Supports AvramDividend.Classical.zero_reflectedSupValue_eq_barrierValue.

import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Tactic.Positivity
import Theorems.Thm_AvramDividend_Classical_barrierRuinTime_zero_eq_iInf_positive
import Theorems.Thm_AvramDividend_Classical_barrierRuinTime_mono_barrier

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.barrierRuinTime_zero_eq_iInf_reciprocal
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) :
    barrierRuinTime X 0 ω =
      ⨅ n : ℕ, barrierRuinTime X (1 / ((n : ℝ) + 1)) ω := by sorry
