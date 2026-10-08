-- Prove2me | Theorems.Thm_ConvexOptimization_weighted_unit_lintegral_eq_iSup_grid
-- name    : ConvexOptimization.weighted_unit_lintegral_eq_iSup_grid
-- status  : Proved
-- author  : @Yifan Hong
-- created : 2026-08-15T07:50:57.426906+00:00
-- url     : https://prove2.me/theorems/18704eb9-1f14-4a5d-b914-78e8c9fe9457
-- title:
--   Uniform layer-cake grid sums recover weighted lower integrals
-- statement:
--   Let $0<\lambda<1$ and let $f,g:\mathbb R\to[0,\infty]$ be measurable functions bounded above by one. For $N\ge1$, put $\delta_N=1/(N+1)$ and define
--
--   $$
--   A_{i,N}=\{x:(i+1)\delta_N\le f(x)\},\qquad
--   B_{i,N}=\{y:(i+1)\delta_N\le g(y)\}
--   $$
--
--   for $0\le i<N$. Then the weighted lower integrals are recovered by the supremum of the uniform lower layer-cake sums:
--
--   $$
--   (1-\lambda)\int_{\mathbb R}f(x)\,dx+\lambda\int_{\mathbb R}g(x)\,dx
--   =
--   \sup_{N\ge1}\delta_N\sum_{i=0}^{N-1}
--   \big((1-\lambda)|A_{i,N}|+\lambda|B_{i,N}|\big).
--   $$
--
--   This is a uniform-grid form of the layer-cake representation and separates the analytic limiting step from finite-level geometric estimates.
--
--   **Formalization Note** The equality is stated in the extended nonnegative reals and uses lower Lebesgue integrals.
-- source:
--   R. J. Gardner, The Brunn-Minkowski Inequality, https://faculty.gardner.wwu.edu/gorizia12.pdf, PDF p. 5, equations (4)-(5), and Theorem 4.1 first proof, PDF pp. 6-7; the finite uniform sums are the lower level-set sums for equation (5).

import Theorems.Thm_ConvexOptimization_brunn_minkowski_real_line_weighted

open scoped RealInnerProductSpace ENNReal
open MeasureTheory

theorem ConvexOptimization.weighted_unit_lintegral_eq_iSup_grid
    (l : ℝ) (hl0 : 0 < l) (hl1 : l < 1)
    (f g : ℝ → ℝ≥0∞)
    (hf : Measurable f) (hg : Measurable g)
    (hf1 : ∀ x, f x ≤ 1) (hg1 : ∀ x, g x ≤ 1) :
    ENNReal.ofReal (1 - l) * (∫⁻ x, f x) +
        ENNReal.ofReal l * (∫⁻ x, g x) =
      ⨆ N : {N : ℕ // 0 < N},
        (((N.1 + 1 : ℕ) : ℝ≥0∞)⁻¹ *
          ∑ i : Fin N.1,
            (ENNReal.ofReal (1 - l) * volume
                {x : ℝ | (((i.val + 1 : ℕ) : ℝ≥0∞) / (N.1 + 1 : ℕ)) ≤ f x} +
              ENNReal.ofReal l * volume
                {y : ℝ | (((i.val + 1 : ℕ) : ℝ≥0∞) / (N.1 + 1 : ℕ)) ≤ g y})) := by
  sorry
