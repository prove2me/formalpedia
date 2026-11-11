-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gfinite51_cap_strip_measure_tendsto_zero
-- name    : AvramDividend.Classical.avram_gfinite51_cap_strip_measure_tendsto_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T22:12:06.271766+00:00
-- url     : https://prove2.me/theorems/c8b4118b-7fe4-4432-b49c-e464a7bc56d5
-- title:
--   Shrinking Gaussian cap-strip occupation has vanishing measure
-- statement:
--   In a finite measure space, if a measurable prepayment reserve Y is almost surely strictly below the finite cap c, then the measure of the strip above any monotone sequence b_j increasing to c tends to zero. This is the non-stochastic occupation step needed to control the finite-cap Gaussian strip martingale energy via an eventual uniform bound on w'.

import Mathlib
open MeasureTheory Set Filter
open scoped ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_gfinite51_cap_strip_measure_tendsto_zero
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (Y : Ω → ℝ) (hY : Measurable Y)
    (c : ℝ) (b : ℕ → ℝ) (hbmono : Monotone b)
    (hb : Tendsto b atTop (𝓝 c))
    (hCapNull : μ {ω | c ≤ Y ω} = 0) :
    Tendsto (fun j : ℕ => μ {ω | b j < Y ω})
      atTop (𝓝 (0 : ℝ≥0∞)) := by
  sorry
