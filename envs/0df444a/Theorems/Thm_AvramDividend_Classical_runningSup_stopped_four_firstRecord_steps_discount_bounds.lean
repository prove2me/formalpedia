-- Prove2me | Theorems.Thm_AvramDividend_Classical_runningSup_stopped_four_firstRecord_steps_discount_bounds
-- name    : AvramDividend.Classical.runningSup_stopped_four_firstRecord_steps_discount_bounds
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T16:44:10.70462+00:00
-- url     : https://prove2.me/theorems/a8326a82-93c5-4ff5-a18d-3053b19c36c1
-- title:
--   Four-record-cell stopped dividend bound over one merged interval
-- statement:
--   For four successive finite attained record increments of h, surviving up to the final record time, the actual discounted stopped Stieltjes payout over the complete half-open time interval from the first to the fifth record lies between the four right-end and four left-end discounted h-sums. This combines the Proved four-cell pair inequality with exact stopped half-open interval additivity.
-- source:
--   Follows the previously Proved two-window four-cell inequality and stopped_lintegral_Ioc_adjacent_add; no independence or Markov assertion is used.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_runningSup_stopped_four_firstRecord_steps_discount_pair_bounds
import Theorems.Thm_AvramDividend_Classical_stopped_lintegral_Ioc_adjacent_add
open MeasureTheory Set
open scoped NNReal ENNReal Classical
open AvramDividend.Classical

theorem AvramDividend.Classical.runningSup_stopped_four_firstRecord_steps_discount_bounds
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
       if r ∈ Set.Ioc (u : ℝ) (k : ℝ)
       then ENNReal.ofReal (Real.exp (-(q * r))) else 0
       ∂(dividendMeasure (runningSup X) ω))) ∧
    ((∫⁻ r in paymentTimes τ,
       if r ∈ Set.Ioc (u : ℝ) (k : ℝ)
       then ENNReal.ofReal (Real.exp (-(q * r))) else 0
       ∂(dividendMeasure (runningSup X) ω)) ≤
     (ENNReal.ofReal (Real.exp (-(q * (u : ℝ)))) * ENNReal.ofReal h +
      ENNReal.ofReal (Real.exp (-(q * (v : ℝ)))) * ENNReal.ofReal h) +
     (ENNReal.ofReal (Real.exp (-(q * (z : ℝ)))) * ENNReal.ofReal h +
      ENNReal.ofReal (Real.exp (-(q * (w : ℝ)))) * ENNReal.ofReal h)) := by sorry
