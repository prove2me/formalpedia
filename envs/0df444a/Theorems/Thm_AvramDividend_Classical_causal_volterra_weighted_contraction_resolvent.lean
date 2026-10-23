-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_volterra_weighted_contraction_resolvent
-- name    : AvramDividend.Classical.causal_volterra_weighted_contraction_resolvent
-- status  : Open
-- author  : @WillR
-- created : 2026-10-22T17:13:24.759388+00:00
-- url     : https://prove2.me/theorems/12f92577-80c1-4a87-9b0e-548c31030f24
-- title:
--   Continuous resolvent from a weighted causal convolution contraction
-- statement:
--   Assume λ>0 and the exponentially weighted causal kernel has norm |β|/λ + integral_0^∞ |K(t)|exp(-λt)dt less than a>0. On the Banach space of continuous functions g:[0,∞)→R with finite norm ||g||_λ=sup_{x≥0} exp(-λx)|g(x)|, consider the affine operator Tg(x)=a⁻¹[1−integral_0^x (β+K(x-s))g(s)ds]. Causal convolution is continuous and has weighted operator norm bounded by a⁻¹ times the given weighted kernel norm, so T is a strict contraction. The Banach fixed-point theorem supplies a unique continuous g satisfying a g+causal convolution=1, including g(0)=1/a. Restricting the fixed point to positive times establishes the precise result.
-- source:
--   Banach fixed-point theorem on an exponentially weighted supremum-norm space of continuous functions and the L1-Linfty Young convolution inequality.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.causal_volterra_weighted_contraction_resolvent
    (K : ℝ → ℝ) (a β weight : ℝ)
    (ha : 0 < a)
    (hweight : 0 < weight)
    (hK : IntegrableOn K (Ioi (0 : ℝ)) volume)
    (hsmall : |β| / weight +
      (∫ t in Ioi (0 : ℝ),
        |K t| * Real.exp (-weight * t) ∂volume) < a) :
    ∃ g : ℝ → ℝ,
      ContinuousOn g (Ici (0 : ℝ)) ∧
      (∀ x : ℝ, 0 < x →
        a * g x +
          (∫ s in Ioc (0 : ℝ) x,
            (β + K (x - s)) * g s ∂volume) = 1) := by sorry
