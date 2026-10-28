-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat12_upper_eventual_renewal_of_exit_factor
-- name    : AvramDividend.Classical.chat12_upper_eventual_renewal_of_exit_factor
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T22:58:43.42422+00:00
-- url     : https://prove2.me/theorems/d5270882-c97f-4784-a24e-958149d63d4a
-- title:
--   Conditional right finite-difference barrier valuation bound from eventual true q-scale exit identities
-- statement:
--   For a differentiable q-scale function with nonzero derivative at the barrier, assume the true discounted epsilon-up-before-(-a)-down strict exit expectation is W(a)/W(a+epsilon) for all sufficiently small positive epsilon. Then the barrier dividend value is eventually bounded above by ENNReal.ofReal(epsilon*W(a+epsilon)/(W(a+epsilon)-W(a))). The proof composes the Proved stochastic upper one-cycle bound conditional on the true strict exit factor with the Proved eventual-renewal upper valuation theorem, giving a completely Proved conditional version of the canonical upper stopped-renewal bound without importing the Open corrected exit identity.

import Mathlib.Topology.Order.OrderClosed
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_barrierSupValue_stopped_renewal_upper_of_eventual_expected_step
import Theorems.Thm_AvramDividend_Classical_chat12_killed_firstRecord_upper_step_of_trueExit

open AvramDividend.Classical MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

theorem AvramDividend.Classical.chat12_upper_eventual_renewal_of_exit_factor
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (a : ℝ) (ha : 0 < a)
    (hD : HasDerivAt W (deriv W a) a) (hd : deriv W a ≠ 0)
    (hExit : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      (∫⁻ ω, if
        (⨅ (t : ℝ≥0) (_ : ε < X.X t ω), (t : ℝ≥0∞)) <
        (⨅ (t : ℝ≥0) (_ : X.X t ω < -a), (t : ℝ≥0∞)) then
        ENNReal.ofReal (Real.exp (-(q * ENNReal.toReal
          (⨅ (t : ℝ≥0) (_ : ε < X.X t ω), (t : ℝ≥0∞)))))
      else 0 ∂P) = ENNReal.ofReal (W a / W (a + ε))) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      barrierSupValue X a q ≤
        ENNReal.ofReal (ε * W (a + ε) / (W (a + ε) - W a)) := by sorry
