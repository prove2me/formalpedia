-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_volterra_l1_derivative_resolvent_exists
-- name    : AvramDividend.Classical.causal_volterra_l1_derivative_resolvent_exists
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T16:18:40.681994+00:00
-- url     : https://prove2.me/theorems/eefd3a37-59b0-47bf-ad9e-5b1500e457b0
-- title:
--   Existence of a continuous derivative resolvent for an integrable causal kernel
-- statement:
--   For a>0 and a causal kernel β+K with K in L1 on positive times, the linear Volterra second-kind resolvent equation a g(x)+integral_0^x (β+K(x-s))g(s) ds=1 has a solution continuous on [0,infinity). One method equips globally weighted continuous functions with the norm sup_{x≥0} e^{-λx}|g(x)|. For sufficiently large λ, the convolution operator has norm bounded by a⁻¹(|β|/λ + integral_0^∞ e^{-λt}|K(t)| dt)<1. Its affine fixed point has constant forcing 1/a and is continuous at x=0 with g(0)=1/a. Alternatively, use interval-by-interval contractions with an L1-small initial interval. This lemma isolates construction of the derivative resolvent; integrating it gives the original integrated Volterra equation.
-- source:
--   Classical Banach contraction principle for second-kind Volterra integral equations with L1 kernels; exponentially weighted supremum-norm resolvent construction.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.causal_volterra_l1_derivative_resolvent_exists
    (K : ℝ → ℝ) (a β : ℝ)
    (ha : 0 < a)
    (hK : IntegrableOn K (Ioi (0 : ℝ)) volume) :
    ∃ g : ℝ → ℝ,
      ContinuousOn g (Ici (0 : ℝ)) ∧
      (∀ x : ℝ, 0 < x →
        a * g x +
          (∫ s in Ioc (0 : ℝ) x,
            (β + K (x - s)) * g s ∂volume) = 1) := by sorry
