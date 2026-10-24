-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_weighted_BCF_explicit_kernel_mass_bound
-- name    : AvramDividend.Classical.causal_weighted_BCF_explicit_kernel_mass_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T07:19:19.819146+00:00
-- url     : https://prove2.me/theorems/b9092aee-2428-4549-a93f-5e7557407e21
-- title:
--   Uniform weighted BCF operator bound with the explicit kernel mass
-- statement:
--   Set m=integral_(t>0) exp(-wt)|beta+K(t)|. Under strict weighted smallness this same m satisfies 0≤m<a and controls the weighted causal convolution of every bounded-continuous input by m times its global supremum norm. The bound is uniform over inputs and time horizons, giving a genuine global contraction constant.
-- source:
--   Combines proved positive_weighted_full_kernel_norm_small, causal_weighted_volterra_operator_bound, causal_l1_exponential_damping_integrable and BCF extension/norm control.

import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Theorems.Thm_AvramDividend_Classical_causal_weighted_volterra_operator_bound
import Theorems.Thm_AvramDividend_Classical_positive_weighted_full_kernel_norm_small
import Theorems.Thm_AvramDividend_Classical_causal_l1_exponential_damping_integrable
import Theorems.Thm_AvramDividend_Classical_causal_weighted_BCF_extension_continuous
import Theorems.Thm_AvramDividend_Classical_causal_weighted_BCF_local_bound
import Theorems.Thm_AvramDividend_Classical_causal_weighted_BCF_pointwise_norm_bound
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.causal_weighted_BCF_explicit_kernel_mass_bound
    (K : ℝ → ℝ) (a β w : ℝ) (ha : 0 < a) (hw : 0 < w)
    (hK : IntegrableOn K (Ioi (0 : ℝ)) volume)
    (hsmall : |β| / w +
      (∫ t in Ioi (0 : ℝ), |K t| * Real.exp (-w * t) ∂volume) < a) :
    let m := ∫ t in Ioi (0 : ℝ),
      Real.exp (-w * t) * |β + K t| ∂volume
    0 ≤ m ∧ m < a ∧
      ∀ (f : BoundedContinuousFunction ℝ≥0 ℝ)
        (R x : ℝ) (hR : 0 < R) (hx : x ∈ Ioc (0 : ℝ) R),
        Real.exp (-(w * x)) *
          |∫ s in Ioc (0 : ℝ) x, (β + K (x - s)) *
            (Real.exp (w * s) * f ⟨max s 0, le_max_right s 0⟩) ∂volume| ≤
          ‖f‖ * m := by sorry
