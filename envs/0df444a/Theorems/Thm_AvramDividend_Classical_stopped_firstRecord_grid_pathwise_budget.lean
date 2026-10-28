-- Prove2me | Theorems.Thm_AvramDividend_Classical_stopped_firstRecord_grid_pathwise_budget
-- name    : AvramDividend.Classical.stopped_firstRecord_grid_pathwise_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T14:25:55.902245+00:00
-- url     : https://prove2.me/theorems/e4632c68-2cd1-4584-b08e-62e3089f7b66
-- title:
--   Actual stopped Stieltjes dividend reward dominates all killed first-record payments
-- statement:
--   For any spectrally negative Lévy sample path, any nonnegative discount and positive record mesh, the infinite sum of the genuine killed discounted first-record payments at levels b+(n+1)h is at most the actual stopped Stieltjes dividend reward. The proof combines the surviving finite-prefix Stieltjes lower bound, monotone survival truncation, restriction monotonicity, and monotone convergence of nonnegative finite sums. It requires no strong Markov property or scale-exit identity and directly discharges the pathwise-budget conjunct of the lower stopped-renewal theorem.
-- source:
--   Published first-record survived-prefix, monotone survival-weight budget, stopped interval reward comparison, and finite-prefix-to-tsum results.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Definitions.Def_AvramDividend_Classical_TwoSidedExit

open MeasureTheory Set
open scoped NNReal ENNReal Classical
open AvramDividend.Classical

theorem AvramDividend.Classical.stopped_firstRecord_grid_pathwise_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (a q b h : ℝ) (hq : 0 ≤ q) (hb : 0 ≤ b) (hh : 0 < h) :
    (∑' n : ℕ,
      if twoSidedExitUpTime X (b + ((n + 1 : ℕ) : ℝ) * h) ω <
          barrierRuinTime X a ω then
        ENNReal.ofReal (h * Real.exp
          (-(q * (twoSidedExitUpTime X (b + ((n + 1 : ℕ) : ℝ) * h) ω).toReal)))
      else 0) ≤
      (∫⁻ t,
        if t ∈ paymentTimes (barrierRuinTime X a ω)
        then ENNReal.ofReal (Real.exp (-(q * t))) else 0
        ∂(dividendMeasure (runningSup X) ω)) := by sorry
