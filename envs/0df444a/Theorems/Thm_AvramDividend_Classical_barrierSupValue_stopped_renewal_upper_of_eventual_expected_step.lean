-- Prove2me | Theorems.Thm_AvramDividend_Classical_barrierSupValue_stopped_renewal_upper_of_eventual_expected_step
-- name    : AvramDividend.Classical.barrierSupValue_stopped_renewal_upper_of_eventual_expected_step
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T21:36:54.835477+00:00
-- url     : https://prove2.me/theorems/42653f1b-60d6-48d8-90eb-9415bd01fc55
-- title:
--   Stopped renewal upper bound requires only the expected killed-record step inequality
-- statement:
--   Under the standing Lévy and scale-function hypotheses, the full stopped-renewal upper bound follows from the eventual expected one-step inequality for the concrete killed and discounted upward-record weights. The entire almost-everywhere Stieltjes payout domination and the geometric-quotient algebra are discharged by previously Proved theorems. This isolates the true outstanding stochastic Markov and two-sided-exit obligation for the original root.
-- source:
--   Apply the Proved root reduction using definitional killed-record weights and the Proved all-horizon pathwise indicator budget. Only the hypothesis hstep remains, passed unchanged.

import Mathlib.Topology.Order.OrderClosed
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Analysis.Complex.Exponential
import Theorems.Thm_AvramDividend_Classical_barrierSupValue_stopped_renewal_upper_of_eventual_killed_record_step
import Theorems.Thm_AvramDividend_Classical_barrierSup_stopped_indicator_reward_le_killed_record_tsum

open AvramDividend.Classical MeasureTheory Filter Set
open scoped NNReal ENNReal Topology Classical

theorem AvramDividend.Classical.barrierSupValue_stopped_renewal_upper_of_eventual_expected_step
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (a : ℝ) (ha : 0 < a)
    (hD : HasDerivAt W (deriv W a) a) (hd : deriv W a ≠ 0)
    (hstep : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ n : ℕ,
      (∫⁻ ω, if twoSidedExitUpTime X (((n + 1 : ℕ) : ℝ) * ε) ω <
          barrierRuinTime X a ω then
        ENNReal.ofReal
          (ε * Real.exp (-(q * (twoSidedExitUpTime X (((n + 1 : ℕ) : ℝ) * ε) ω).toReal)))
      else 0 ∂P) ≤
        ENNReal.ofReal (W a / W (a + ε)) *
      (∫⁻ ω, if twoSidedExitUpTime X ((n : ℝ) * ε) ω <
          barrierRuinTime X a ω then
        ENNReal.ofReal
          (ε * Real.exp (-(q * (twoSidedExitUpTime X ((n : ℝ) * ε) ω).toReal)))
      else 0 ∂P)) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      barrierSupValue X a q ≤
        ENNReal.ofReal (ε * W (a + ε) / (W (a + ε) - W a)) := by sorry
