-- Prove2me | Theorems.Thm_AvramDividend_Classical_stopped_discounted_drift_tail_layercake
-- name    : AvramDividend.Classical.stopped_discounted_drift_tail_layercake
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T17:41:29.522347+00:00
-- url     : https://prove2.me/theorems/79b63391-883f-465b-8c17-5e21e9b9a167
-- title:
--   Expected continuously discounted drift reward up to a real stopping time equals its strict-survival tail integral
-- statement:
--   Let tau be any measurable nonnegative real stopping-clock random variable and d>=0 a constant drift payout rate. The expectation of the nonnegative discounted drift integral d*exp(-q*t) over [0,tau(omega)] equals the Lebesgue integral over positive t of d*exp(-q*t) multiplied by the strict survival probability P(t<tau). The statement holds for any real q as local interval integrability is enough and does not require independent increments or finite expected tau. It is an application of pinned Mathlib's strict Cavalieri/layer-cake theorem lintegral_comp_eq_lintegral_meas_lt_mul, with continuous exponential payoff and nonnegative integrand. This supplies a reusable probabilistic Tonelli bridge for Avram finite-activity zero-reflected dividend valuation, initially for a real stopping clock; compact truncation handles ENNReal-valued ruin clocks.
-- source:
--   Tonelli/Cavalieri layer-cake formula, pinned Mathlib MeasureTheory.Integral.Layercake; Avram Palmowski Pistorius 2007 §3.3 stopped dividends.

import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.FunProp

open MeasureTheory Set

theorem AvramDividend.Classical.stopped_discounted_drift_tail_layercake
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (τ : Ω → ℝ) (hτ : Measurable τ)
    (hNonneg : ∀ᵐ ω ∂P, 0 ≤ τ ω)
    (d q : ℝ) (hd : 0 ≤ d) :
    (∫⁻ ω, ENNReal.ofReal
        (∫ t in (0 : ℝ)..τ ω, d * Real.exp (-(q * t))) ∂P) =
      ∫⁻ t in Ioi (0 : ℝ),
        P {ω : Ω | t < τ ω} *
          ENNReal.ofReal (d * Real.exp (-(q * t))) := by sorry
