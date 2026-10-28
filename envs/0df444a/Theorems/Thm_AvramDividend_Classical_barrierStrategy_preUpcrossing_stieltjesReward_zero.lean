-- Prove2me | Theorems.Thm_AvramDividend_Classical_barrierStrategy_preUpcrossing_stieltjesReward_zero
-- name    : AvramDividend.Classical.barrierStrategy_preUpcrossing_stieltjesReward_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T17:26:22.519371+00:00
-- url     : https://prove2.me/theorems/d51daf55-975d-4c98-9513-af1eb941f9a7
-- title:
--   All discounted and undiscounted Stieltjes barrier rewards vanish before the first upper passage
-- statement:
--   For any nonnegative extended-real reward weight, including exponential discounting, the Stieltjes dividend integral over the full closed time interval from 0 through the first finite upward passage is zero. The first passage generates no pre-exit dividends, so the strong-Markov value decomposition may restrict its reward to later times.
-- source:
--   Immediate pathwise integral bridge for W-free dividendValue_barrierStrategy_upExit_split_of_standing 79978d61-9d1f-4b20-b8a5-114797a8e380; uses zero closed-window Stieltjes measure theorem currently being proved, and the existing Mathlib setLIntegral_measure_zero.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_dividendMeasure_zero_through_firstUpcrossing

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.barrierStrategy_preUpcrossing_stieltjesReward_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x a : ℝ) (hx0 : 0 ≤ x) (hxa : x ≤ a)
    (ω : Ω) (u : ℝ≥0)
    (hu : (u : ℝ≥0∞) =
      (⨅ (s : ℝ≥0) (_ : a - x < X.X s ω), (s : ℝ≥0∞)))
    (f : ℝ → ℝ≥0∞) :
    (∫⁻ t in Set.Icc (0 : ℝ) (u : ℝ), f t
      ∂(dividendMeasure (barrierStrategy X x a) ω)) = 0 := by
  sorry
