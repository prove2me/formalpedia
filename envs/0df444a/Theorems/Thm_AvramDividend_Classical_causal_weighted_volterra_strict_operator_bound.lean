-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_weighted_volterra_strict_operator_bound
-- name    : AvramDividend.Classical.causal_weighted_volterra_strict_operator_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T06:49:34.029985+00:00
-- url     : https://prove2.me/theorems/dc2670cf-06f6-453a-854f-2f634713d867
-- title:
--   A single strict weighted mass bounds every finite-horizon causal Volterra convolution
-- statement:
--   For positive a and exponential weight w, an L1 kernel with weighted drift-plus-kernel mass less than a has one nonnegative m<a bounding the exponentially weighted causal convolution on every finite horizon. The mass is independent of the input, time horizon and evaluation point, which is the estimate needed to build a strict contraction on a weighted function space.
-- source:
--   Combines three formally proved Prove2Me lemmas: exponential damping integrability, small full weighted kernel norm, and the weighted operator bound.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Theorems.Thm_AvramDividend_Classical_causal_l1_exponential_damping_integrable
import Theorems.Thm_AvramDividend_Classical_positive_weighted_full_kernel_norm_small
import Theorems.Thm_AvramDividend_Classical_causal_weighted_volterra_operator_bound
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.causal_weighted_volterra_strict_operator_bound
    (K V : ℝ → ℝ) (a β w : ℝ)
    (ha : 0 < a) (hw : 0 < w)
    (hK : IntegrableOn K (Ioi (0 : ℝ)) volume)
    (hsmall : |β| / w + (∫ t in Ioi (0 : ℝ), |K t| * Real.exp (-w * t) ∂volume) < a)
    (hVc : ContinuousOn V (Ioi (0 : ℝ)))
    (hVb : ∀ R : ℝ, 0 < R → ∃ C : ℝ, ∀ s : ℝ, s ∈ Ioc (0 : ℝ) R → |V s| ≤ C) :
    ∃ m : ℝ, 0 ≤ m ∧ m < a ∧
      ∀ (R x : ℝ) (hR : 0 < R) (hx : x ∈ Ioc (0 : ℝ) R),
        Real.exp (-(w * x)) *
          |∫ s in Ioc (0 : ℝ) x, (β + K (x - s)) * V s ∂volume| ≤
        sSup ((fun t : ℝ => Real.exp (-(w * t)) * |V t|) '' Ioc (0 : ℝ) R) * m := by sorry
