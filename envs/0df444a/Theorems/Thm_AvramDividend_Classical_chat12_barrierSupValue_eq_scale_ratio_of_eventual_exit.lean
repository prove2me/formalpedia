-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat12_barrierSupValue_eq_scale_ratio_of_eventual_exit
-- name    : AvramDividend.Classical.chat12_barrierSupValue_eq_scale_ratio_of_eventual_exit
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T23:13:59.380524+00:00
-- url     : https://prove2.me/theorems/15c40005-064f-46f4-98ed-8b93cd166904
-- title:
--   Exact barrier dividend q-scale ratio value from eventual strict two-sided exit identities
-- statement:
--   Assuming a differentiable q-scale function with nonzero derivative at a positive barrier, and both true discounted strict up-before-down exit-factor identities for all sufficiently small record increments, prove barrierSupValue X a q = ENNReal.ofReal(W(a)/W'(a)). It composes the independent upper and lower eventual conditional renewal bounds with the fully Proved derivative-sandwich valuation theorem. The stochastic q-scale exit identities are explicit hypotheses, rather than imports of the still-Open corrected theorem.

import Mathlib.Topology.Order.OrderClosed
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_barrierSupValue_of_stopped_renewal_bounds
import Theorems.Thm_AvramDividend_Classical_chat12_upper_eventual_renewal_of_exit_factor
import Theorems.Thm_AvramDividend_Classical_chat12_lower_eventual_renewal_of_exit_factor

open AvramDividend.Classical MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat12_barrierSupValue_eq_scale_ratio_of_eventual_exit
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (a : ℝ) (ha : 0 < a)
    (hD : HasDerivAt W (deriv W a) a) (hd : deriv W a ≠ 0)
    (hUpExit : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      (∫⁻ ω, if
        (⨅ (t : ℝ≥0) (_ : ε < X.X t ω), (t : ℝ≥0∞)) <
        (⨅ (t : ℝ≥0) (_ : X.X t ω < -a), (t : ℝ≥0∞)) then
        ENNReal.ofReal (Real.exp (-(q * ENNReal.toReal
          (⨅ (t : ℝ≥0) (_ : ε < X.X t ω), (t : ℝ≥0∞)))))
      else 0 ∂P) = ENNReal.ofReal (W a / W (a + ε)))
    (hDownExit : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      (∫⁻ ω, if
        (⨅ (t : ℝ≥0) (_ : ε < X.X t ω), (t : ℝ≥0∞)) <
        (⨅ (t : ℝ≥0) (_ : X.X t ω < ε - a), (t : ℝ≥0∞)) then
        ENNReal.ofReal (Real.exp (-(q * ENNReal.toReal
          (⨅ (t : ℝ≥0) (_ : ε < X.X t ω), (t : ℝ≥0∞)))))
      else 0 ∂P) = ENNReal.ofReal (W (a - ε) / W a)) :
    barrierSupValue X a q =
      ENNReal.ofReal (W a / deriv W a) := by sorry
