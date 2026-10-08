-- Prove2me | Theorems.Thm_ConvexOptimization_leindler_supremal_integral_real_line_unit_sup_normalized_additive
-- name    : ConvexOptimization.leindler_supremal_integral_real_line_unit_sup_normalized_additive
-- status  : Proved
-- author  : @Yifan Hong
-- created : 2026-08-15T06:33:54.091417+00:00
-- url     : https://prove2.me/theorems/e460bdc8-3962-4e0e-8559-c5914c56cc92
-- title:
--   Additive layer-cake core of the normalized Leindler inequality
-- statement:
--   Let $0 < \lambda < 1$, and let $f,g:\mathbb R\to[0,\infty]$ be measurable, compactly supported functions bounded above by one, with pointwise suprema equal to one. Define
--
--   $$
--   R_\lambda(z)=\sup\{f(x)^{1-\lambda}g(y)^\lambda:(1-\lambda)x+\lambda y=z\}.
--   $$
--
--   Then
--
--   $$
--   (1-\lambda)\int_{\mathbb R}f(x)\,dx+\lambda\int_{\mathbb R}g(x)\,dx
--   \le \int_{\mathbb R}R_\lambda(z)\,dz.
--   $$
--
--   This additive form is the source's canonical intermediate inequality and is a reusable analytic core for deriving the multiplicative Prékopa-Leindler bound by weighted arithmetic-geometric mean.
--
--   **Formalization Note** Functions and lower Lebesgue integrals take values in the extended nonnegative reals. The pointwise envelope is represented by the supremum of its attainable values.
-- source:
--   R. J. Gardner, The Brunn-Minkowski Inequality, https://faculty.gardner.wwu.edu/gorizia12.pdf, Theorem 4.1 first proof, PDF pp. 6-7, specifically the displayed additive estimate on p. 7 before the final arithmetic-geometric mean step; using the layer-cake formula (5) on p. 5 and Theorem 2.1, equation (2), on p. 3.

import Theorems.Thm_ConvexOptimization_brunn_minkowski_real_line_weighted

open scoped RealInnerProductSpace ENNReal
open MeasureTheory

theorem ConvexOptimization.leindler_supremal_integral_real_line_unit_sup_normalized_additive
    (l : ℝ) (hl0 : 0 < l) (hl1 : l < 1)
    (f g : ℝ → ℝ≥0∞)
    (hf : Measurable f) (hg : Measurable g)
    (hfc : HasCompactSupport f) (hgc : HasCompactSupport g)
    (hf1 : ∀ x, f x ≤ 1) (hg1 : ∀ x, g x ≤ 1)
    (hfsup : sSup (Set.range f) = 1)
    (hgsup : sSup (Set.range g) = 1) :
    ENNReal.ofReal (1 - l) * (∫⁻ x, f x) +
        ENNReal.ofReal l * (∫⁻ x, g x) ≤
      ∫⁻ z, sSup {q : ℝ≥0∞ | ∃ x y : ℝ,
        (1 - l) • x + l • y = z ∧
          q = f x ^ (1 - l) * g y ^ l} := by sorry
