-- Prove2me | Theorems.Thm_EntropicBarrier_Universal_lemma1_hessian_entropicBarrier
-- name    : EntropicBarrier.Universal.lemma1_hessian_entropicBarrier
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T08:25:51.681484+00:00
-- url     : https://prove2.me/theorems/8f6cf64d-3f73-474f-bc09-6288107ff37c
-- title:
--   Lemma 1 (iv) — $\nabla^2 f^*(x)=\Sigma(\theta(x))^{-1}$, eq. (6)
-- statement:
--   Let $\mathcal K\subset\mathbb R^n$ be a convex body with entropic barrier $f^*$, and let $\theta(x)=\nabla f^*(x)$. For every $x\in\operatorname{int}(\mathcal K)$:
--
--   1. the mean of $p_{\theta(x)}$ is $x$, i.e. $x(\theta(x))=x$;
--   2. for all $h,k\in\mathbb R^n$,
--   $$\nabla^2 f^*(x)\left[\Sigma(\theta(x))h,\;k\right]=\langle h,k\rangle,$$
--   that is, $\nabla^2 f^*(x)=\Sigma(\theta(x))^{-1}=\left(\mathbb E_{X\sim p_{\theta(x)}}(X-x)(X-x)^\top\right)^{-1}$.
--
--   This is eq. (6): the Hessian of the entropic barrier is the inverse covariance of the matching member of the exponential family.
--
--   **Formalization Note** The inverse is encoded without inverting: $\nabla^2 f^*(x)\circ\Sigma(\theta(x))=\mathrm{Id}$ forces $\Sigma(\theta(x))$ to be invertible with inverse $\nabla^2 f^*(x)$. Item 1 is the identity $x(\theta(x))=x$ that the page uses when it writes $(X-x)$ in the middle term of (6). The middle equality $(\nabla^2 f(\theta(x)))^{-1}$ of (6) follows from this and Lemma 1 (iii).
-- source:
--   Bubeck & Eldan, The entropic barrier: a simple and optimal universal self-concordant barrier, arXiv:1412.1587v3 (COLT 2015), p. 5, Lemma 1 (iv), eq. (6)

import Mathlib
import Definitions.Def_EntropicBarrier_Universal_EntropicBarrier
import Definitions.Def_EntropicBarrier_Universal_ExpFamily

open scoped RealInnerProductSpace
open MeasureTheory

namespace EntropicBarrier.Universal

theorem lemma1_hessian_entropicBarrier {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n)))
    (hK : IsConvexBody K) (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ interior K) :
    meanMap K (gradient (entropicBarrier K) x) = x ∧
    ∀ h k : EuclideanSpace ℝ (Fin n),
      iteratedFDeriv ℝ 2 (entropicBarrier K) x
        ![covApply K (gradient (entropicBarrier K) x) h, k] = ⟪h, k⟫ := by sorry

end EntropicBarrier.Universal
