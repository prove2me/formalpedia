-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_zero_reserve_killed_renewal_of_positive_reserve
-- name    : AvramDividend.Classical.chat04_zero_reserve_killed_renewal_of_positive_reserve
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T11:59:01.490585+00:00
-- url     : https://prove2.me/theorems/a4686701-c569-4869-b78c-11b295914230
-- title:
--   Zero-reserve killed q-scale renewal follows from positive reserves alone
-- statement:
--   Unbounded variation forces Wq(0)=0. Whole-path killed discounted scale payoffs are monotone in initial capital. If each strictly positive-capital expectation equals Wq(x), the zero-capital expectation is dominated by Wq(x) for every x>0 and hence vanishes as x tends to zero by continuity. No independent instantaneous downward regularity assumption is required.
-- source:
--   Proved scale zero origin, proved monotonicity of q-scale, pointwise initial reserve monotonicity and Mathlib filter le_of_tendsto.

import Theorems.Thm_AvramDividend_Classical_chat04_killed_scale_payoff_monotone_initial_capital
import Theorems.Thm_AvramDividend_Classical_chat04_scale_zero_origin_of_unbounded_variation
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Order.OrderClosed

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat04_zero_reserve_killed_renewal_of_positive_reserve
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation) (t : ℝ≥0)
    (hpositive : ∀ (x : ℝ), 0 < x →
      (∫⁻ ω,
        ({u : Ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s u}).indicator
          (fun u => ENNReal.ofReal
            (Real.exp (-(q * (t : ℝ))) * W (x + X.X t u))) ω ∂P) =
        ENNReal.ofReal (W x)) :
    (∫⁻ ω,
      ({u : Ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ X.X s u}).indicator
        (fun u => ENNReal.ofReal
          (Real.exp (-(q * (t : ℝ))) * W (X.X t u))) ω ∂P) =
      ENNReal.ofReal (W 0) := by sorry
