-- Prove2me | Theorems.Thm_ConvexOptimization_prekopa_leindler_one_dimensional
-- name    : ConvexOptimization.prekopa_leindler_one_dimensional
-- status  : Proved
-- author  : @Yifan Hong
-- created : 2026-08-14T16:22:50.829424+00:00
-- url     : https://prove2.me/theorems/7a31f6fc-d182-4fa0-8dab-21ed29c3ec8e
-- title:
--   One-dimensional Prékopa–Leindler inequality (lower-integral form)
-- statement:
--   Let $0 < \lambda < 1$, and let $f,g,h : \mathbb{R} \to [0,+\infty]$ be measurable. Assume that for every $x,y \in \mathbb{R}$,
--
--   $$
--   f(x)^{1-\lambda}g(y)^{\lambda} \le h((1-\lambda)x+\lambda y).
--   $$
--
--   Then their lower Lebesgue integrals satisfy
--
--   $$
--   \left(\int f\right)^{1-\lambda}\left(\int g\right)^{\lambda} \le \int h.
--   $$
--
--   This is the extended-nonnegative, lower-integral form of the one-dimensional Prékopa–Leindler inequality, allowing both function values and integrals to be $+\infty$.
-- source:
--   Richard J. Gardner, The Brunn-Minkowski Inequality: A Survey with Proofs, https://faculty.gardner.wwu.edu/gorizia12.pdf, Theorem 4.1 (pp. 6-8), together with the lower-integral extension described in András Prékopa, Logarithmic concave measures with applications to stochastic programming, https://rutcor.rutgers.edu/Prekopa/pdf/SCIENT2.pdf, equations (2.1)-(2.2) and the surrounding extended-integral convention.

import Mathlib

open scoped RealInnerProductSpace ENNReal
open MeasureTheory

theorem ConvexOptimization.prekopa_leindler_one_dimensional
    (l : ℝ) (hl0 : 0 < l) (hl1 : l < 1)
    (f g h : EuclideanSpace ℝ (Fin 1) → ℝ≥0∞)
    (hf : Measurable f) (hg : Measurable g) (hh : Measurable h)
    (hple : ∀ x y : EuclideanSpace ℝ (Fin 1),
      f x ^ (1 - l) * g y ^ l ≤ h ((1 - l) • x + l • y)) :
    (∫⁻ x, f x) ^ (1 - l) * (∫⁻ x, g x) ^ l ≤ ∫⁻ x, h x := by sorry
