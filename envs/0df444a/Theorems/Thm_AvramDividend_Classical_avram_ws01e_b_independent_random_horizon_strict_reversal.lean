-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_independent_random_horizon_strict_reversal
-- name    : AvramDividend.Classical.avram_ws01e_b_independent_random_horizon_strict_reversal
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T01:14:35.389531+00:00
-- url     : https://prove2.me/theorems/83aab0f5-8f42-463f-b9c1-57dcd0e364fa
-- title:
--   Strict terminal Lévy drawdown/minimum reversal at any independent random horizon
-- statement:
--   Let e be any nonnegative independently sampled random observation horizon under a σ-finite clock measure Q. For a spectrally negative Lévy process whose joint strict drawdown and running-infimum events are measurable, the product-law probability that the terminal drawdown falls below a real strict threshold equals that of the running infimum. The result allows e=0, treated directly, and relies on the Proved fixed-horizon strict reversal and independent-clock section integration, without a tilted Lévy law or Wiener–Hopf independence.
-- source:
--   Direct composition of Proved avram_ws01e_b_fixed_horizon_strict_reversal (a0501c79) and avram_ws01e_b_independent_clock_section_probability_transfer (d1f793c0); strict cadlag time reversal and Tonelli.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_independent_clock_section_probability_transfer
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_fixed_horizon_strict_reversal

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01e_b_independent_random_horizon_strict_reversal
    {Ω Θ : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace Θ]
    {P : Measure Ω} [SFinite P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (Q : Measure Θ) [SFinite Q]
    (e : Θ → ℝ≥0) (he : Measurable e)
    (a : ℝ)
    (hL : MeasurableSet {z : Ω × Θ |
      ∃ s : ℝ≥0, s ≤ e z.2 ∧
        X.X (e z.2) z.1 - X.X s z.1 < a})
    (hR : MeasurableSet {z : Ω × Θ |
      ∃ s : ℝ≥0, s ≤ e z.2 ∧
        X.X s z.1 - X.X 0 z.1 < a}) :
    (P.prod Q) {z : Ω × Θ |
      ∃ s : ℝ≥0, s ≤ e z.2 ∧
        X.X (e z.2) z.1 - X.X s z.1 < a} =
    (P.prod Q) {z : Ω × Θ |
      ∃ s : ℝ≥0, s ≤ e z.2 ∧
        X.X s z.1 - X.X 0 z.1 < a} := by sorry
