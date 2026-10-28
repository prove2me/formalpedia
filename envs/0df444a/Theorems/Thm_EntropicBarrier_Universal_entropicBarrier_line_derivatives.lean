-- Prove2me | Theorems.Thm_EntropicBarrier_Universal_entropicBarrier_line_derivatives
-- name    : EntropicBarrier.Universal.entropicBarrier_line_derivatives
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-10-25T13:47:28.048242+00:00
-- url     : https://prove2.me/theorems/a9758187-e9e9-473e-8445-47ef9be291b5
-- title:
--   §4, pp. 6–7 — duality formulas: $f^*$ is convex and $C^3$ on $\operatorname{int}(\mathcal K)$, with $\nabla^2 f^*$ and $\nabla^3 f^*$ given by the moments of $p_\theta$
-- statement:
--   Let $\mathcal K\subset\mathbb R^n$ be a convex body, $f(\theta)=\log\int_{\mathcal K}e^{\langle\theta,x\rangle}dx$ its log-Laplace transform, $f^*$ the entropic barrier, and $p_\theta$ the exponential family with mean $x(\theta)$ and covariance $\Sigma(\theta)$. Then $f^*$ is convex and $C^3$ on $\operatorname{int}(\mathcal K)$, and for every $x\in\operatorname{int}(\mathcal K)$ and $v\in\mathbb R^n$ there are $\theta$ with $x(\theta)=x$ and $h=\Sigma(\theta)^{-1}v$ such that
--
--   $$\nabla^2 f^*(x)[v,v]=\mathbb E_{X\sim p_\theta}\langle X-x,h\rangle^2,\qquad \nabla^3 f^*(x)[v,v,v]=-\,\mathbb E_{X\sim p_\theta}\langle X-x,h\rangle^3 .$$
--
--   That is, $\nabla^2 f^*(x)=\nabla^2 f(\theta)^{-1}$ and $\nabla^3 f^*(x)[v,v,v]=-\nabla^3 f(\theta)[h,h,h]$ at $\theta=\nabla f^*(x)$.
--
--   Role: the Legendre-duality step in the proof that $f^*$ is self-concordant (§4, pp. 6–7); combined with the moment inequality $\mathbb E\langle X-x,h\rangle^3\le 2(\mathbb E\langle X-x,h\rangle^2)^{3/2}$ (applied to $\pm h$) it gives condition (2).
--
--   **Formalization Note**: the derivatives are taken along the line $t\mapsto x+tv$, matching `ConvexOptimization.IsSelfConcordantOn`.
-- source:
--   Bubeck & Eldan, The entropic barrier: a simple and optimal universal self-concordant barrier, arXiv:1412.1587v3 (COLT 2015), https://arxiv.org/abs/1412.1587, §4, pp. 6–7 (derivatives of f* via Lemma 1)

import Mathlib
import Definitions.Def_EntropicBarrier_Universal_EntropicBarrier
import Definitions.Def_EntropicBarrier_Universal_ExpFamily

open scoped RealInnerProductSpace
open MeasureTheory

namespace EntropicBarrier.Universal

theorem entropicBarrier_line_derivatives {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n)))
    (hK : IsConvexBody K) :
    ConvexOn ℝ (interior K) (entropicBarrier K) ∧
    ContDiffOn ℝ 3 (entropicBarrier K) (interior K) ∧
    ∀ x ∈ interior K, ∀ v : EuclideanSpace ℝ (Fin n), ∃ θ h : EuclideanSpace ℝ (Fin n),
      meanMap K θ = x ∧ covApply K θ h = v ∧
      iteratedDeriv 2 (fun t : ℝ => entropicBarrier K (x + t • v)) 0 =
        ∫ y, ⟪y - meanMap K θ, h⟫ ^ 2 ∂(expFamily K θ) ∧
      iteratedDeriv 3 (fun t : ℝ => entropicBarrier K (x + t • v)) 0 =
        -∫ y, ⟪y - meanMap K θ, h⟫ ^ 3 ∂(expFamily K θ) := by sorry

end EntropicBarrier.Universal
