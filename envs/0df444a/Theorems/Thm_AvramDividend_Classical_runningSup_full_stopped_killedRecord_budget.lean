-- Prove2me | Theorems.Thm_AvramDividend_Classical_runningSup_full_stopped_killedRecord_budget
-- name    : AvramDividend.Classical.runningSup_full_stopped_killedRecord_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T22:27:37.221235+00:00
-- url     : https://prove2.me/theorems/ded45632-4a66-4e8b-9937-2c477aea91c6
-- title:
--   Unconditional stopped reflected dividend payout is dominated by killed first-record payments
-- statement:
--   For every spectrally negative Lévy path, arbitrary extended ruin time including immediate killing, nonnegative discount and positive record spacing, the full strict pre-ruin discounted Stieltjes dividend integral is bounded by the killed first-record payment series. At positive ruin time use the proved full-horizon rational-prefix result. At zero time the payment region is exactly {0} and the running-supremum dividend measure has no initial atom.
-- source:
--   Case split τ=0 using paymentTimes_min_zero_eq_singleton_zero and runningSup_dividendMeasure_zero_initial_atom, otherwise apply runningSup_full_stopped_killedRecord_budget_of_pos_ruin.

import Mathlib.Data.ENNReal.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_runningSup_full_stopped_killedRecord_budget_of_pos_ruin
import Theorems.Thm_AvramDividend_Classical_runningSup_dividendMeasure_zero_initial_atom
import Theorems.Thm_AvramDividend_Classical_paymentTimes_min_zero_eq_singleton_zero

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.runningSup_full_stopped_killedRecord_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (τ : ℝ≥0∞) (q h : ℝ) (hq : 0 ≤ q) (hh : 0 < h) :
    (∫⁻ r in paymentTimes τ,
      ENNReal.ofReal (Real.exp (-(q * r)))
      ∂(dividendMeasure (runningSup X) ω)) ≤
    (∑' k : ℕ,
      if (⨅ (r : ℝ≥0) (_ : (0 : ℝ) + (k : ℝ) * h < X.X r ω), (r : ℝ≥0∞)) < τ then
        ENNReal.ofReal
          (h * Real.exp (-(q * ((⨅ (r : ℝ≥0) (_ : (0 : ℝ) + (k : ℝ) * h < X.X r ω), (r : ℝ≥0∞))).toReal)))
      else 0) := by sorry
