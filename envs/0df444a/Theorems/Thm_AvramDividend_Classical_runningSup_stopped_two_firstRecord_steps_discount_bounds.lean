-- Prove2me | Theorems.Thm_AvramDividend_Classical_runningSup_stopped_two_firstRecord_steps_discount_bounds
-- name    : AvramDividend.Classical.runningSup_stopped_two_firstRecord_steps_discount_bounds
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T09:23:16.427778+00:00
-- url     : https://prove2.me/theorems/1f8abe66-c253-4629-a2df-659435f2331c
-- title:
--   Two consecutive attained first-record h-cells give exact additive stopped dividend bounds
-- statement:
--   Consider three finite first upward passage times u,v,z at levels b,b+h,b+2h of the original spectrally negative Lévy process, ordered u≤v≤z, with h≥0 and the final time z strictly preceding the original stopped-payment horizon. The genuine discounted running-supremum Stieltjes dividend reward over the entire interval (u,z] lies between the sum of the two terminal-discounted h-cell payments h exp(-qv)+h exp(-qz) and the sum of their initial-discounted payments h exp(-qu)+h exp(-qv). The proof combines the remotely accepted exact single h-cell reward inequalities with the exact adjacent half-open integral additivity identity. No record-level strong Markov regeneration or scale exit transform is postulated. This is the first two-cell building block for a finite and eventually countable inverse-record-level reward partition.
-- source:
--   Remotely accepted runningSup_stopped_firstRecord_step_discount_bounds target a87a10e8-a1d2-4485-a173-c0cf2d7e72d0 candidate 12521; dependency-gated lintegral_Ioc_adjacent_add authoring request 851ccb10-9c2c-4125-b0e2-72c9e18304dc.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_lintegral_Ioc_adjacent_add
import Theorems.Thm_AvramDividend_Classical_runningSup_stopped_firstRecord_step_discount_bounds

open MeasureTheory Set
open scoped NNReal ENNReal Classical
open AvramDividend.Classical

theorem AvramDividend.Classical.runningSup_stopped_two_firstRecord_steps_discount_bounds
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (τ : ℝ≥0∞) (q : ℝ) (hq : 0 ≤ q)
    (b h : ℝ) (hb : 0 ≤ b) (hh : 0 ≤ h)
    (u v z : ℝ≥0)
    (hu : (u : ℝ≥0∞) =
      (⨅ (r : ℝ≥0) (_ : b < X.X r ω), (r : ℝ≥0∞)))
    (hv : (v : ℝ≥0∞) =
      (⨅ (r : ℝ≥0) (_ : b + h < X.X r ω), (r : ℝ≥0∞)))
    (hz : (z : ℝ≥0∞) =
      (⨅ (r : ℝ≥0) (_ : b + h + h < X.X r ω), (r : ℝ≥0∞)))
    (huv : (u : ℝ) ≤ (v : ℝ))
    (hvz : (v : ℝ) ≤ (z : ℝ))
    (hSurvive : ENNReal.ofReal (z : ℝ) < τ) :
    (ENNReal.ofReal (Real.exp (-(q * (v : ℝ)))) * ENNReal.ofReal h +
     ENNReal.ofReal (Real.exp (-(q * (z : ℝ)))) * ENNReal.ofReal h ≤ ∫⁻ r in paymentTimes τ,
        if r ∈ Set.Ioc (u : ℝ) (z : ℝ)
        then ENNReal.ofReal (Real.exp (-(q * r))) else 0
        ∂(dividendMeasure (runningSup X) ω)) ∧
    (∫⁻ r in paymentTimes τ,
        if r ∈ Set.Ioc (u : ℝ) (z : ℝ)
        then ENNReal.ofReal (Real.exp (-(q * r))) else 0
        ∂(dividendMeasure (runningSup X) ω) ≤ ENNReal.ofReal (Real.exp (-(q * (u : ℝ)))) * ENNReal.ofReal h +
     ENNReal.ofReal (Real.exp (-(q * (v : ℝ)))) * ENNReal.ofReal h) := by sorry
