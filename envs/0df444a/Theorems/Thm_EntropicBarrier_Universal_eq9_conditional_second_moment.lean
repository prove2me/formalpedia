-- Prove2me | Theorems.Thm_EntropicBarrier_Universal_eq9_conditional_second_moment
-- name    : EntropicBarrier.Universal.eq9_conditional_second_moment
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T08:04:04.228887+00:00
-- url     : https://prove2.me/theorems/80edd979-78f9-4d3f-a487-9f863980a867
-- title:
--   §4, eq. (9) — $\mathbb E(|Y-y_0|^2\mid|Y-y_0|\le M)\le\sigma^2$
-- statement:
--   Under the hypotheses and notation of Lemma 3 ($n\ge80$, $\mathcal K$ a convex body, $\theta\ne0$, $\rho$ the density of $Y=\langle\theta/\|\theta\|,X\rangle$, smooth in the interior of its support, $y_0$ a maximizer of $\rho$, and $M,\sigma^2$ as there),
--   $$\mathbb E\left(|Y-y_0|^2\ \middle|\ |Y-y_0|\le M\right)\le\sigma^2,$$
--   stated as
--   $$\int_{\{|y-y_0|\le M\}}(y-y_0)^2\rho(y)\,dy\ \le\ \sigma^2\int_{\{|y-y_0|\le M\}}\rho(y)\,dy.$$
--
--   **Formalization Note** The conditional expectation is written in product form (numerator $\le\sigma^2\cdot$ denominator), which is equivalent because the denominator is positive ($\rho(y_0)>0$ and $\rho$ is positive near $y_0$), and avoids a division that Lean would evaluate as $0$ if the denominator vanished. Smoothness of $\rho$ is the same explicit hypothesis as in Lemma 3.
-- source:
--   Bubeck & Eldan, The entropic barrier: a simple and optimal universal self-concordant barrier, arXiv:1412.1587v3 (COLT 2015), p. 8, §4, eq. (9)

import Mathlib
import Definitions.Def_EntropicBarrier_Universal_EntropicBarrier
import Definitions.Def_EntropicBarrier_Universal_Marginal

open scoped RealInnerProductSpace
open MeasureTheory
open scoped ContDiff

namespace EntropicBarrier.Universal

theorem eq9_conditional_second_moment {n : ℕ} (hn : 80 ≤ n)
    (K : Set (EuclideanSpace ℝ (Fin n)))
    (hK : IsConvexBody K) (θ : EuclideanSpace ℝ (Fin n)) (hθ : θ ≠ 0)
    (hsmooth : ContDiffOn ℝ ∞ (projDensity K θ) (interior {y | 0 < projDensity K θ y}))
    (y₀ : ℝ) (hy₀ : ∀ y, projDensity K θ y ≤ projDensity K θ y₀) :
    ∫ y in {y : ℝ | |y - y₀| ≤ Real.sqrt (7 * n * Real.log n) / ‖θ‖},
        (y - y₀) ^ 2 * projDensity K θ y ≤
      ((n : ℝ) / ‖θ‖ ^ 2 * (1 / (1 - Real.sqrt (7 * Real.log n / n)))) *
        ∫ y in {y : ℝ | |y - y₀| ≤ Real.sqrt (7 * n * Real.log n) / ‖θ‖},
          projDensity K θ y := by sorry

end EntropicBarrier.Universal
