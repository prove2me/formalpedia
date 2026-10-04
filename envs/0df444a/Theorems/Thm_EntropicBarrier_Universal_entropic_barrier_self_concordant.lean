-- Prove2me | Theorems.Thm_EntropicBarrier_Universal_entropic_barrier_self_concordant
-- name    : EntropicBarrier.Universal.entropic_barrier_self_concordant
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T08:04:39.799895+00:00
-- url     : https://prove2.me/theorems/0ac54f14-6508-4534-b419-d3dd56b04e9c
-- title:
--   Theorem 1 — the entropic barrier is a $(1+\varepsilon_n)n$-self-concordant barrier, $\varepsilon_n\le100\sqrt{\log(n)/n}$, $n\ge80$
-- statement:
--   Let $n\ge80$ and let $\mathcal K\subset\mathbb R^n$ be a convex body (compact, convex, non-empty interior). Let
--   $$f(\theta)=\log\left(\int_{x\in\mathcal K}\exp(\langle\theta,x\rangle)\,dx\right),\qquad\theta\in\mathbb R^n,$$
--   and let $f^*(x)=\sup_{\theta\in\mathbb R^n}\langle\theta,x\rangle-f(\theta)$ for $x\in\operatorname{int}(\mathcal K)$. Then $f^*$ is a $\nu$-self-concordant barrier on $\mathcal K$ with
--   $$\nu=(1+\varepsilon_n)\,n,\qquad\varepsilon_n=100\sqrt{\frac{\log(n)}{n}}:$$
--
--   1. $f^*(x)\to+\infty$ as $x\to\partial\mathcal K$;
--   2. $f^*$ is $C^3$-smooth and convex on $\operatorname{int}(\mathcal K)$ with $\nabla^3 f^*(x)[h,h,h]\le2(\nabla^2 f^*(x)[h,h])^{3/2}$;
--   3. $\nabla f^*(x)[h]\le\sqrt{\nu\cdot\nabla^2 f^*(x)[h,h]}$ for all $x\in\operatorname{int}(\mathcal K)$, $h\in\mathbb R^n$.
--
--   This gives an explicit universal barrier for convex bodies with parameter $(1+o(1))n$, which is optimal up to the second-order term since $\nu\ge n$ is necessary for some bodies (simplex, cube).
--
--   **Formalization Note** The page says "a $(1+\varepsilon_n)n$-self-concordant barrier with $\varepsilon_n\le100\sqrt{\log(n)/n}$". Condition (3) is monotone in $\nu$ (its right side grows with $\nu$ and the Hessian of a convex function is non-negative), so stating it with $\varepsilon_n$ equal to its bound is the same claim; it is not weakened to an existential $\nu$. $\mathbb R^n$ is `EuclideanSpace ℝ (Fin n)`, so $n$ is the dimension. $\log(n)/n>0$ for $n\ge80$, so the square root is the true one. The interior of $\mathcal K$ is non-empty by definition, so the statement is not vacuous; no smoothness of $\mathcal K$ is assumed.
-- source:
--   Bubeck & Eldan, The entropic barrier: a simple and optimal universal self-concordant barrier, arXiv:1412.1587v3 (COLT 2015), p. 1, Theorem 1 (proof §4, pp. 6-9, and §5, pp. 10-13)

import Mathlib
import Definitions.Def_EntropicBarrier_Universal_EntropicBarrier
import Definitions.Def_ConvexOptimization_selfConcordance
import Definitions.Def_EntropicBarrier_Universal_SelfConcordantBarrier

open scoped RealInnerProductSpace
open MeasureTheory

namespace EntropicBarrier.Universal

theorem entropic_barrier_self_concordant {n : ℕ} (hn : 80 ≤ n)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsConvexBody K) :
    IsNuSelfConcordantBarrier K (entropicBarrier K)
      ((1 + 100 * Real.sqrt (Real.log n / n)) * n) := by sorry

end EntropicBarrier.Universal
