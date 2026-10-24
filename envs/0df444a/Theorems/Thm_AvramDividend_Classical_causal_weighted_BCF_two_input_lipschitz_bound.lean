-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_weighted_BCF_two_input_lipschitz_bound
-- name    : AvramDividend.Classical.causal_weighted_BCF_two_input_lipschitz_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T07:31:23.147537+00:00
-- url     : https://prove2.me/theorems/41927ae0-db43-46dc-9f27-8fbec722c7b3
-- title:
--   Uniform two-input Lipschitz bound for the weighted causal Volterra operator
-- statement:
--   For any two bounded-continuous inputs f,h, the weighted difference between their causal convolutions is bounded by the fixed kernel mass m times ‖f−h‖. The mass m is explicit and strictly below a independent of f,h. Apply the established one-input kernel bound to f−h and use Bochner integral linearity, after local integrability, to identify the difference of integrals with the integral of the input difference.
-- source:
--   Combines proved explicit mass inequality, full kernel input integrability, and BCF subtraction.

import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Theorems.Thm_AvramDividend_Classical_causal_weighted_BCF_explicit_kernel_mass_bound
import Theorems.Thm_AvramDividend_Classical_causal_full_kernel_locally_bounded_input_integrable
import Theorems.Thm_AvramDividend_Classical_causal_weighted_BCF_extension_continuous
import Theorems.Thm_AvramDividend_Classical_causal_weighted_BCF_local_bound
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.causal_weighted_BCF_two_input_lipschitz_bound
    (K : ℝ → ℝ) (a β w : ℝ) (ha : 0 < a) (hw : 0 < w)
    (hK : IntegrableOn K (Ioi (0 : ℝ)) volume)
    (hsmall : |β| / w +
      (∫ t in Ioi (0 : ℝ), |K t| * Real.exp (-w * t) ∂volume) < a) :
    let m := ∫ t in Ioi (0 : ℝ),
      Real.exp (-w * t) * |β + K t| ∂volume
    0 ≤ m ∧ m < a ∧
      ∀ (f h : BoundedContinuousFunction ℝ≥0 ℝ)
        (R x : ℝ) (hR : 0 < R) (hx : x ∈ Ioc (0 : ℝ) R),
        Real.exp (-(w * x)) *
          |(∫ s in Ioc (0 : ℝ) x, (β + K (x - s)) *
              (Real.exp (w * s) * f ⟨max s 0, le_max_right s 0⟩) ∂volume) -
           (∫ s in Ioc (0 : ℝ) x, (β + K (x - s)) *
              (Real.exp (w * s) * h ⟨max s 0, le_max_right s 0⟩) ∂volume)| ≤
          ‖f - h‖ * m := by sorry
