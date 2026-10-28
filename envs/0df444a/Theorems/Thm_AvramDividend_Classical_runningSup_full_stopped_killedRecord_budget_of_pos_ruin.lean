-- Prove2me | Theorems.Thm_AvramDividend_Classical_runningSup_full_stopped_killedRecord_budget_of_pos_ruin
-- name    : AvramDividend.Classical.runningSup_full_stopped_killedRecord_budget_of_pos_ruin
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T22:16:10.999051+00:00
-- url     : https://prove2.me/theorems/fa3e21da-f522-428a-bc56-880d95827db5
-- title:
--   The complete pre-ruin running-supremum reward is bounded by the killed first-record series
-- statement:
--   On every path with strictly positive ruin horizon, the full killed stopped Stieltjes reward of the running supremum is at most the infinite series of discounted record-grid payments. Extend the Proved surviving finite-horizon estimate to all strict rational payment prefixes, handle the zero-time atom, and apply the countable directed exhaustion of stopped payment times. This supplies the exact pathwise bound needed for upper renewal verification.
-- source:
--   Composition of surviving finite-horizon killed record budgets, zero initial Stieltjes atom, Ico-to-Ioc integral comparison, payment-time survival and rational-prefix integral exhaustion.

import Mathlib.Data.ENNReal.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_runningSup_surviving_finite_horizon_killedRecord_budget
import Theorems.Thm_AvramDividend_Classical_paymentTimes_lintegral_le_of_rational_prefix_bounds
import Theorems.Thm_AvramDividend_Classical_lintegral_Ico_le_Ioc_of_zero_initial_atom
import Theorems.Thm_AvramDividend_Classical_runningSup_dividendMeasure_zero_initial_atom
import Theorems.Thm_AvramDividend_Classical_paymentTimes_Ioc_subset_of_terminal_survival

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.runningSup_full_stopped_killedRecord_budget_of_pos_ruin
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (τ : ℝ≥0∞) (q h : ℝ) (hq : 0 ≤ q) (hh : 0 < h)
    (hτ : 0 < τ) :
    (∫⁻ r in paymentTimes τ,
      ENNReal.ofReal (Real.exp (-(q * r)))
      ∂(dividendMeasure (runningSup X) ω)) ≤
    (∑' k : ℕ,
      if (⨅ (r : ℝ≥0) (_ : (0 : ℝ) + (k : ℝ) * h < X.X r ω), (r : ℝ≥0∞)) < τ then
        ENNReal.ofReal
          (h * Real.exp (-(q * ((⨅ (r : ℝ≥0) (_ : (0 : ℝ) + (k : ℝ) * h < X.X r ω), (r : ℝ≥0∞))).toReal)))
      else 0) := by sorry
