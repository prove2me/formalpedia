-- Prove2me | Theorems.Thm_AvramDividend_Classical_barrierStrategy_upExit_before_controlledRuin_iff_rawExit
-- name    : AvramDividend.Classical.barrierStrategy_upExit_before_controlledRuin_iff_rawExit
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T10:00:23.996602+00:00
-- url     : https://prove2.me/theorems/374d2f8d-4a88-4360-9ecd-419f18e9759d
-- title:
--   Unconditional strict successful barrier exit equals raw two-sided upper-before-lower exit
-- statement:
--   For a spectrally negative Lévy path started with nonnegative capital below a positive dividend barrier, the strict first upward-passage clock precedes the controlled ruin clock exactly when it precedes the raw downward ruin clock. Unlike the finite-u pathwise result, this theorem directly uses extended-nonnegative infimum first-passage clocks and covers the no-upcrossing/infinite-clock case. It is the event-normalisation bridge needed in the standing-only strong-Markov barrier dividend-value factorisation.
-- source:
--   Accepted pathwise success equivalence AvramDividend.Classical.barrierStrategy_successful_upcrossing_iff_raw_lower_exit (6883dd6c-a050-4e3b-8839-28515104cfd9), extended by the ENNReal finite/infinite case split. Mathematical interface for Open theorem dividendValue_barrierStrategy_upExit_split_of_standing (79978d61-9d1f-4b20-b8a5-114797a8e380).

import Mathlib.Data.ENNReal.Basic
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_successful_upcrossing_iff_raw_lower_exit
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.barrierStrategy_upExit_before_controlledRuin_iff_rawExit
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x a : ℝ) (ha : 0 < a) (hx0 : 0 ≤ x) (hxa : x ≤ a)
    (ω : Ω) :
    (⨅ (s : ℝ≥0) (_ : a - x < X.X s ω), (s : ℝ≥0∞)) <
        ruinTime X x (barrierStrategy X x a) ω ↔
      (⨅ (s : ℝ≥0) (_ : a - x < X.X s ω), (s : ℝ≥0∞)) <
        (⨅ (t : ℝ≥0) (_ : X.X t ω < -x), (t : ℝ≥0∞)) := by sorry
