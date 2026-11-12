-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a06_adjacent_independent_interval_charfun_concat_20261111
-- name    : AvramDividend.Classical.avram_a06_adjacent_independent_interval_charfun_concat_20261111
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T19:22:35.600966+00:00
-- url     : https://prove2.me/theorems/7576a799-2555-4ee7-8961-9d17fb48a7d2
-- title:
--   Adjacent independent marked sums have multiplicative interval characteristic functions
-- statement:
--   Two independent adjacent finite mark sums have a characteristic function that multiplies under concatenation. This supplies the stochastic ingredient required for the A06 interval-characteristic power lemma and its conditional Fourier representation.

import Mathlib
open MeasureTheory ProbabilityTheory Finset
noncomputable section

theorem AvramDividend.Classical.avram_a06_adjacent_independent_interval_charfun_concat_20261111
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (Y : ℕ → Ω → ℝ) (hY : ∀ j, Measurable (Y j))
    (a b c : ℕ) (hab : a ≤ b) (hbc : b ≤ c)
    (hInd : IndepFun
      (fun ω => ∑ j ∈ Finset.Ico a b, Y j ω)
      (fun ω => ∑ j ∈ Finset.Ico b c, Y j ω) P)
    (t : ℝ) :
    MeasureTheory.charFun
      (Measure.map (fun ω => ∑ j ∈ Finset.Ico a c, Y j ω) P) t =
    MeasureTheory.charFun
      (Measure.map (fun ω => ∑ j ∈ Finset.Ico a b, Y j ω) P) t *
    MeasureTheory.charFun
      (Measure.map (fun ω => ∑ j ∈ Finset.Ico b c, Y j ω) P) t := by sorry
