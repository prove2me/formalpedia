-- Prove2me | Theorems.Thm_AvramDividend_Classical_runningSup_finite_horizon_last_record_stopped_upper
-- name    : AvramDividend.Classical.runningSup_finite_horizon_last_record_stopped_upper
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T20:09:46.402988+00:00
-- url     : https://prove2.me/theorems/33bc540a-563d-4a17-9b35-567c941f3786
-- title:
--   Stopped terminal record-cell budget at every last finite-horizon record
-- statement:
--   When the grid record at level b+N h is the final strict upcrossing before a finite horizon t, and t itself precedes the stopping time, there exist finite ordered record times representing all reached grid levels. The discounted stopped Stieltjes dividends after the first record and through t are bounded by the sum of initial-record discounted h-increments. This discharges the attained-record branch of finite-horizon renewal discretisation without requiring the next grid clock to be finite.
-- source:
--   Combines the proved finite record-clock realisation with the proved N complete record cells plus extended terminal-cell bound, using the last-clock horizon condition to control the end interval.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Theorems.Thm_AvramDividend_Classical_firstRecord_grid_finite_clocks_realisable_before_horizon
import Theorems.Thm_AvramDividend_Classical_runningSup_finite_record_cells_with_terminal_discount_upper

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal Classical

theorem AvramDividend.Classical.runningSup_finite_horizon_last_record_stopped_upper
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (τ : ℝ≥0∞) (q b h : ℝ)
    (hq : 0 ≤ q) (hb : 0 ≤ b) (hh : 0 < h)
    (N : ℕ) (t : ℝ≥0)
    (hN : (⨅ (r : ℝ≥0)
      (_ : b + (N : ℝ) * h < X.X r ω), (r : ℝ≥0∞)) <
      (t : ℝ≥0∞))
    (hnext : ¬ (⨅ (r : ℝ≥0)
      (_ : b + ((N + 1 : ℕ) : ℝ) * h < X.X r ω),
      (r : ℝ≥0∞)) < (t : ℝ≥0∞))
    (htτ : (t : ℝ≥0∞) < τ) :
    ∃ u : ℕ → ℝ≥0,
      (∀ k : ℕ, k ≤ N →
        (u k : ℝ≥0∞) =
          (⨅ (r : ℝ≥0)
            (_ : b + (k : ℝ) * h < X.X r ω), (r : ℝ≥0∞))) ∧
      (∫⁻ r in paymentTimes τ,
        if r ∈ Set.Ioc (u 0 : ℝ) (t : ℝ)
        then ENNReal.ofReal (Real.exp (-(q * r))) else 0
        ∂(dividendMeasure (runningSup X) ω)) ≤
      ∑ k ∈ Finset.range (N + 1),
        ENNReal.ofReal (Real.exp (-(q * (u k : ℝ)))) *
          ENNReal.ofReal h := by sorry
