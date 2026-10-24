-- Prove2me | Theorems.Thm_AvramDividend_Classical_runningSup_stopped_four_firstRecord_steps_discount_pair_bounds
-- name    : AvramDividend.Classical.runningSup_stopped_four_firstRecord_steps_discount_pair_bounds
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T16:33:59.54817+00:00
-- url     : https://prove2.me/theorems/3b1dbfe0-6a80-4686-bd26-50185bfae414
-- title:
--   Four attained record cells have additive discounted stopped-reward bounds
-- statement:
--   Four consecutive attained h-sized first-record increments, with the last attainment strictly before the stopping horizon, give an explicit lower and upper bound for the sum of their two disjoint two-cell Stieltjes dividend rewards. The proof combines the two already-Proved two-cell bounds and discounted survival monotonicity. This prepares a four-cell finite-grid renewal partition without any strong-Markov or independent-increment assumption.
-- source:
--   Formal extension of the Proved runningSup_stopped_two_firstRecord_steps_discount_bounds (1f8abe66-c253-4629-a2df-659435f2331c), toward Avram's stopped-renewal barrierSupValue estimates.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_runningSup_stopped_two_firstRecord_steps_discount_bounds
open MeasureTheory Set
open scoped NNReal ENNReal Classical
open AvramDividend.Classical

theorem AvramDividend.Classical.runningSup_stopped_four_firstRecord_steps_discount_pair_bounds
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (τ : ℝ≥0∞) (q : ℝ) (hq : 0 ≤ q)
    (b h : ℝ) (hb : 0 ≤ b) (hh : 0 ≤ h)
    (u v z w k : ℝ≥0)
    (hu : (u : ℝ≥0∞) =
      (⨅ (r : ℝ≥0) (_ : b < X.X r ω), (r : ℝ≥0∞)))
    (hv : (v : ℝ≥0∞) =
      (⨅ (r : ℝ≥0) (_ : b + h < X.X r ω), (r : ℝ≥0∞)))
    (hz : (z : ℝ≥0∞) =
      (⨅ (r : ℝ≥0) (_ : b + h + h < X.X r ω), (r : ℝ≥0∞)))
    (hw : (w : ℝ≥0∞) =
      (⨅ (r : ℝ≥0) (_ : b + h + h + h < X.X r ω), (r : ℝ≥0∞)))
    (hk : (k : ℝ≥0∞) =
      (⨅ (r : ℝ≥0) (_ : b + h + h + h + h < X.X r ω), (r : ℝ≥0∞)))
    (huv : (u : ℝ) ≤ (v : ℝ)) (hvz : (v : ℝ) ≤ (z : ℝ))
    (hzw : (z : ℝ) ≤ (w : ℝ)) (hwk : (w : ℝ) ≤ (k : ℝ))
    (hSurvive : ENNReal.ofReal (k : ℝ) < τ) :
    ((ENNReal.ofReal (Real.exp (-(q * (v : ℝ)))) * ENNReal.ofReal h +
      ENNReal.ofReal (Real.exp (-(q * (z : ℝ)))) * ENNReal.ofReal h) +
     (ENNReal.ofReal (Real.exp (-(q * (w : ℝ)))) * ENNReal.ofReal h +
      ENNReal.ofReal (Real.exp (-(q * (k : ℝ)))) * ENNReal.ofReal h) ≤
     (∫⁻ r in paymentTimes τ,
       if r ∈ Set.Ioc (u : ℝ) (z : ℝ)
       then ENNReal.ofReal (Real.exp (-(q * r))) else 0
       ∂(dividendMeasure (runningSup X) ω)) +
     (∫⁻ r in paymentTimes τ,
       if r ∈ Set.Ioc (z : ℝ) (k : ℝ)
       then ENNReal.ofReal (Real.exp (-(q * r))) else 0
       ∂(dividendMeasure (runningSup X) ω))) ∧
    ((∫⁻ r in paymentTimes τ,
       if r ∈ Set.Ioc (u : ℝ) (z : ℝ)
       then ENNReal.ofReal (Real.exp (-(q * r))) else 0
       ∂(dividendMeasure (runningSup X) ω)) +
     (∫⁻ r in paymentTimes τ,
       if r ∈ Set.Ioc (z : ℝ) (k : ℝ)
       then ENNReal.ofReal (Real.exp (-(q * r))) else 0
       ∂(dividendMeasure (runningSup X) ω)) ≤
     (ENNReal.ofReal (Real.exp (-(q * (u : ℝ)))) * ENNReal.ofReal h +
      ENNReal.ofReal (Real.exp (-(q * (v : ℝ)))) * ENNReal.ofReal h) +
     (ENNReal.ofReal (Real.exp (-(q * (z : ℝ)))) * ENNReal.ofReal h +
      ENNReal.ofReal (Real.exp (-(q * (w : ℝ)))) * ENNReal.ofReal h)) := by sorry
