-- Prove2me | Theorems.Thm_FatkhullinPolyak_Flow_lqr_gradient_formula
-- name    : FatkhullinPolyak.Flow.lqr_gradient_formula
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T12:45:11.891197+00:00
-- url     : https://prove2.me/theorems/032eddac-0f11-4ec5-bdb2-962e1b0b08e0
-- title:
--   Lemma 3.11 — the gradient of the LQR cost is $2(RKC-B^\top X)YC^\top$
-- statement:
--   Let $Q, R, \Sigma\succ0$ and let $K\in\mathcal S$ be a stabilizing gain. Then the LQR cost $f$ is (Fréchet) differentiable at $K$, and its derivative is the linear functional
--   $$E \;\longmapsto\; \mathrm{Tr}\big(\nabla f(K)^\top E\big) = \langle \nabla f(K), E\rangle_F,\qquad \nabla f(K) = 2\,(RKC - B^\top X(K))\,Y(K)\,C^\top,$$
--   where $X(K)$ solves (2.7) and $Y(K)$ solves the Lyapunov equation (3.4) $A_KY + YA_K^\top + \Sigma = 0$.
--
--   In other words, (3.3) is the gradient of $f$ with respect to the Frobenius inner product $\langle M, N\rangle = \mathrm{Tr}(M^\top N)$, so the flow (4.1) is the gradient flow of $f$.
--
--   **Formalization Note** Differentiability is taken with respect to the Frobenius norm on $\mathbb R^{m\times r}$ (Mathlib's `Matrix.frobeniusNormedAddCommGroup`, used as a local instance); all norms on this finite-dimensional space give the same notion. The standing assumptions $\operatorname{rank}C=r$ and $B\ne0$ are not needed for this statement and are omitted, which makes it only stronger.
-- source:
--   Fatkhullin, Polyak, Optimizing Static Linear Feedback: Gradient Method, arXiv:2004.09875v2, p. 7, Lemma 3.11, (3.3)–(3.4)

import Mathlib
import Definitions.Def_FatkhullinPolyak_Flow_LQR

namespace FatkhullinPolyak.Flow

open Matrix

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

theorem lqr_gradient_formula {n m r : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ) (C : Matrix (Fin r) (Fin n) ℝ)
    (Q : Matrix (Fin n) (Fin n) ℝ) (R : Matrix (Fin m) (Fin m) ℝ) (Sig : Matrix (Fin n) (Fin n) ℝ)
    (hQ : Q.PosDef) (hR : R.PosDef) (hSig : Sig.PosDef)
    (K : Matrix (Fin m) (Fin r) ℝ) (hK : K ∈ stabSet A B C) :
    ∃ f' : Matrix (Fin m) (Fin r) ℝ →L[ℝ] ℝ,
      HasFDerivAt (fun K' => cost A B C Q R Sig K') f' K ∧
        ∀ E : Matrix (Fin m) (Fin r) ℝ, f' E = trace ((grad A B C Q R Sig K)ᵀ * E) := by sorry

end FatkhullinPolyak.Flow
