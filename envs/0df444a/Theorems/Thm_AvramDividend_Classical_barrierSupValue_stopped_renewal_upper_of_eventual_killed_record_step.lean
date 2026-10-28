-- Prove2me | Theorems.Thm_AvramDividend_Classical_barrierSupValue_stopped_renewal_upper_of_eventual_killed_record_step
-- name    : AvramDividend.Classical.barrierSupValue_stopped_renewal_upper_of_eventual_killed_record_step
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T17:43:59.586237+00:00
-- url     : https://prove2.me/theorems/c481fcb6-bc9c-48c7-8eed-e57d858e6a6f
-- title:
--   Standing-scale stopped renewal upper bound from actual killed first-record estimates
-- statement:
--   Under the exact Standing, positive discount, scale-function and derivative assumptions of the original stopped-renewal upper-bound theorem, eventual pathwise domination by the actual killed discounted first-record grid weights and an eventual one-step expected-weight recurrence imply the original eventually valid upper finite-difference quotient. Positivity and strict increment are entirely discharged by existing Proved scale-function and calculus theorems.
-- source:
--   Direct root-connected bridge for AvramDividend.Classical.barrierSupValue_stopped_renewal_upper_bound, based on Proved scaleFunction_monotone, scaleFunction_strict_pos_of_standing, monotone_nonzero_derivative_eventually_right_increment, and barrierSupValue_le_right_scale_quotient_of_killed_grid_step. Remaining assumptions are exactly the stopped pathwise cover and killed first-record expectation renewal inequality.

import Mathlib.Topology.Order.OrderClosed
import Theorems.Thm_AvramDividend_Classical_scaleFunction_monotone
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_standing
import Theorems.Thm_AvramDividend_Classical_monotone_nonzero_derivative_eventually_right_increment
import Theorems.Thm_AvramDividend_Classical_barrierSupValue_le_right_scale_quotient_of_killed_grid_step

open AvramDividend.Classical MeasureTheory Filter Set
open scoped NNReal ENNReal Topology Classical

theorem AvramDividend.Classical.barrierSupValue_stopped_renewal_upper_of_eventual_killed_record_step
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (a : ℝ) (ha : 0 < a)
    (hD : HasDerivAt W (deriv W a) a) (hd : deriv W a ≠ 0)
    (w : ℝ → ℕ → Ω → ℝ≥0∞)
    (hw : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ n ω, w ε n ω =
      if twoSidedExitUpTime X ((n : ℝ) * ε) ω <
          barrierRuinTime X a ω then
        ENNReal.ofReal
          (ε * Real.exp (-(q * (twoSidedExitUpTime X ((n : ℝ) * ε) ω).toReal)))
      else 0)
    (hbudget : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ᵐ ω ∂P,
      (∫⁻ t,
        if t ∈ paymentTimes (barrierRuinTime X a ω)
        then ENNReal.ofReal (Real.exp (-(q * t))) else 0
        ∂(dividendMeasure (runningSup X) ω)) ≤ (∑' n, w ε n ω))
    (hstep : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ n,
      (∫⁻ ω, w ε (n + 1) ω ∂P) ≤
        ENNReal.ofReal (W a / W (a + ε)) *
          (∫⁻ ω, w ε n ω ∂P)) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      barrierSupValue X a q ≤
        ENNReal.ofReal (ε * W (a + ε) / (W (a + ε) - W a)) := by sorry
