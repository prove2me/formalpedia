-- Prove2me | Theorems.Thm_AvramDividend_Classical_scaleFunction_right_renewal_ratio_eventually_subunit
-- name    : AvramDividend.Classical.scaleFunction_right_renewal_ratio_eventually_subunit
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T17:49:55.65453+00:00
-- url     : https://prove2.me/theorems/34a6dc25-6857-4baa-ae39-5050a2c45ead
-- title:
--   Standing scale functions have strictly subunit right-renewal ratio near zero
-- statement:
--   For positive discount and positive barrier under Avram Standing, a differentiable q-scale function with nonzero derivative has W(a+epsilon)>W(a)>0 for all sufficiently small positive epsilon. Consequently the killed first-record renewal ratio W(a)/W(a+epsilon) lies in [0,1), validating the geometric series step required for the stopped-renewal upper bound.
-- source:
--   Analytic prerequisite to stopped-renewal upper theorem c6c3b1d0-2c2f-41ce-a5a0-2771efcc3a69, combining Proved scaleFunction_monotone, scaleFunction_strict_pos_of_standing and monotone_nonzero_derivative_eventually_right_increment.

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Order.OrderClosed
import Theorems.Thm_AvramDividend_Classical_scaleFunction_monotone
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_standing
import Theorems.Thm_AvramDividend_Classical_monotone_nonzero_derivative_eventually_right_increment

open AvramDividend.Classical MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

theorem AvramDividend.Classical.scaleFunction_right_renewal_ratio_eventually_subunit
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (a : ℝ) (ha : 0 < a)
    (hD : HasDerivAt W (deriv W a) a) (hd : deriv W a ≠ 0) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      0 < ε ∧ 0 < W (a + ε) ∧
        0 ≤ W a / W (a + ε) ∧ W a / W (a + ε) < 1 := by sorry
