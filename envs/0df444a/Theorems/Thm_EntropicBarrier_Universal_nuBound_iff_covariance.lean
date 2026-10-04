-- Prove2me | Theorems.Thm_EntropicBarrier_Universal_nuBound_iff_covariance
-- name    : EntropicBarrier.Universal.nuBound_iff_covariance
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T08:26:20.925981+00:00
-- url     : https://prove2.me/theorems/39b70c27-5375-4cfd-a60a-fe1fc168c8a2
-- title:
--   §4, p. 7 — (3) for $f^*$ with parameter $\nu$ $\iff$ $\langle\Sigma(\theta)\theta,\theta\rangle\le\nu$ for all $\theta$
-- statement:
--   Let $\mathcal K\subset\mathbb R^n$ be a convex body with entropic barrier $f^*$ and covariance map $\Sigma(\theta)$ of its exponential family, and let $\nu\ge0$. Then $f^*$ satisfies condition (3) with parameter $\nu$, i.e.
--   $$\nabla f^*(x)[h]\le\sqrt{\nu\cdot\nabla^2 f^*(x)[h,h]}\qquad\text{for all }x\in\operatorname{int}(\mathcal K),\ h\in\mathbb R^n,$$
--   if and only if
--   $$\langle\Sigma(\theta)\theta,\theta\rangle\le\nu\qquad\text{for all }\theta\in\mathbb R^n.$$
--
--   This reduces the self-concordance parameter of $f^*$ to a variance bound for the exponential family.
--
--   **Formalization Note** $\nu\ge0$ is implicit on the page ($\nu$ is a parameter of size about $n$). For $\nu<0$ the square root of a negative number is $0$ in Lean and the equivalence would fail for a junk reason. $\langle\Sigma(\theta)\theta,\theta\rangle$ is `covForm K θ θ θ`.
-- source:
--   Bubeck & Eldan, The entropic barrier: a simple and optimal universal self-concordant barrier, arXiv:1412.1587v3 (COLT 2015), p. 7, §4, reduction of (3)

import Mathlib
import Definitions.Def_EntropicBarrier_Universal_EntropicBarrier
import Definitions.Def_ConvexOptimization_selfConcordance
import Definitions.Def_EntropicBarrier_Universal_SelfConcordantBarrier
import Definitions.Def_EntropicBarrier_Universal_ExpFamily

open scoped RealInnerProductSpace
open MeasureTheory

namespace EntropicBarrier.Universal

theorem nuBound_iff_covariance {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n)))
    (hK : IsConvexBody K) (ν : ℝ) (hν : 0 ≤ ν) :
    SatisfiesNuBound K (entropicBarrier K) ν ↔
      ∀ θ : EuclideanSpace ℝ (Fin n), covForm K θ θ θ ≤ ν := by sorry

end EntropicBarrier.Universal
