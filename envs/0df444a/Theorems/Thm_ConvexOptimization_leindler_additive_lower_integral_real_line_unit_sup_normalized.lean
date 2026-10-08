-- Prove2me | Theorems.Thm_ConvexOptimization_leindler_additive_lower_integral_real_line_unit_sup_normalized
-- name    : ConvexOptimization.leindler_additive_lower_integral_real_line_unit_sup_normalized
-- status  : Proved
-- author  : @Yifan Hong
-- created : 2026-08-15T07:08:04.970667+00:00
-- url     : https://prove2.me/theorems/82f8b1a8-c568-40ed-b2e0-88724cbd0d1b
-- title:
--   Additive normalized Leindler inequality for a pointwise majorant
-- statement:
--   Let $0 < \lambda < 1$. Let $f,g:\mathbb R\to[0,\infty]$ be measurable, compactly supported functions bounded above by one, with pointwise suprema equal to one. Let $h:\mathbb R\to[0,\infty]$ be any function satisfying
--
--   $$
--   f(x)^{1-\lambda}g(y)^\lambda\le h((1-\lambda)x+\lambda y)
--   $$
--
--   for every $x,y\in\mathbb R$. Then
--
--   $$
--   (1-\lambda)\int_{\mathbb R}f(x)\,dx+\lambda\int_{\mathbb R}g(x)\,dx
--   \le \int_{\mathbb R}h(z)\,dz.
--   $$
--
--   This is the additive layer-cake core of the normalized one-dimensional Prékopa--Leindler inequality. It is reusable for pointwise supremal envelopes and preserves contributions supported on null sets.
--
--   **Formalization Note** All functions and lower Lebesgue integrals are extended-nonnegative-real-valued. No measurability hypothesis is imposed on $h$; the lower integral is the appropriate formulation for pointwise majorants.
-- source:
--   R. J. Gardner, The Brunn-Minkowski Inequality, https://faculty.gardner.wwu.edu/gorizia12.pdf, Theorem 4.1 first proof, PDF pp. 6-7, specifically the displayed additive estimate on p. 7; using the layer-cake formula (5) on p. 5 and the one-dimensional Brunn-Minkowski inequality, Theorem 2.1 equation (2), on p. 3. The lower-integral formulation retains the pointwise level-set argument discussed in Section 9, pp. 16-18.

import Theorems.Thm_ConvexOptimization_brunn_minkowski_real_line_weighted

open scoped RealInnerProductSpace ENNReal
open MeasureTheory

theorem ConvexOptimization.leindler_additive_lower_integral_real_line_unit_sup_normalized
    (l : ℝ) (hl0 : 0 < l) (hl1 : l < 1)
    (f g h : ℝ → ℝ≥0∞)
    (hf : Measurable f) (hg : Measurable g)
    (hfc : HasCompactSupport f) (hgc : HasCompactSupport g)
    (hf1 : ∀ x, f x ≤ 1) (hg1 : ∀ x, g x ≤ 1)
    (hfsup : sSup (Set.range f) = 1)
    (hgsup : sSup (Set.range g) = 1)
    (hmajor : ∀ x y : ℝ,
      f x ^ (1 - l) * g y ^ l ≤ h ((1 - l) • x + l • y)) :
    ENNReal.ofReal (1 - l) * (∫⁻ x, f x) +
        ENNReal.ofReal l * (∫⁻ x, g x) ≤
      ∫⁻ z, h z := by sorry
