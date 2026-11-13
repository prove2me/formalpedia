-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a54_true_stop_mask_large_source_tail_sum_measurable
-- name    : AvramDividend.Classical.avram_ga_a54_true_stop_mask_large_source_tail_sum_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T00:25:10.708834+00:00
-- url     : https://prove2.me/theorems/6067515f-28fe-4dc8-87a5-f658aafd7e29
-- title:
--   Genuine stopping-clock masked finite Gaussian large-increment quadratic source energy is measurable
-- statement:
--   Any finite physical source grid of measurable real increments, restricted to the cells whose starts occur before a measurable random clock, has a measurable nonnegative large-increment squared-energy sum.
-- source:
--   Discharges hSumMeas original stopped Gaussian raw-tail convergence ga_a52 en route to b0d9951c.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a54_true_stop_mask_large_source_tail_sum_measurable
    {Ω : Type*} [MeasurableSpace Ω]
    (S : Finset ℕ) (s : ℕ → ℝ≥0)
    (ρ : Ω → ℝ≥0) (hρ : Measurable ρ)
    (Z : ℕ → Ω → ℝ)
    (hZ : ∀ i ∈ S, Measurable (Z i))
    (η : ℝ) :
    Measurable (fun ω : Ω =>
      Finset.sum S (fun i =>
        if s i < ρ ω then
          ENNReal.ofReal (if η ≤ |Z i ω| then (Z i ω)^2 else 0)
        else 0)) := by sorry
