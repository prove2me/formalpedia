-- Prove2me | Theorems.Thm_FatkhullinPolyak_Flow_flow_energy_identity
-- name    : FatkhullinPolyak.Flow.flow_energy_identity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T12:46:46.749757+00:00
-- url     : https://prove2.me/theorems/3ce7b05a-c5e1-4add-8945-cc6875bfca1c
-- title:
--   §4.1 — along the gradient flow, $\frac{d}{dt}f(K_t) = -\|\nabla f(K_t)\|_F^2$
-- statement:
--   Let $Q, R, \Sigma\succ0$ and let $K_t = K(t)$ be a solution on $[0,\infty)$ of the gradient flow (4.1), $\dot K = -\nabla f(K)$, $K(0)=K_0$ (in particular $K_t\in\mathcal S$ for all $t\ge0$). Then for every $t\ge0$ the function $s\mapsto f(K_s)$ is differentiable at $t$ (from the right at $t=0$) with
--   $$\frac{d}{dt} f(K_t) = -\|\nabla f(K_t)\|_F^2 .$$
--
--   This energy identity is "the main idea of the proof" of Theorem 4.1: it shows at once that $f(K_t)$ is nonincreasing.
--
--   **Formalization Note** The derivative is taken within $[0,\infty)$. The norm is the Frobenius norm, the one with respect to which (3.3) is the gradient.
-- source:
--   Fatkhullin, Polyak, Optimizing Static Linear Feedback: Gradient Method, arXiv:2004.09875v2, p. 10, §4.1, last paragraph; Appendix D.1, p. 18

import Mathlib
import Definitions.Def_FatkhullinPolyak_Flow_LQR
import Definitions.Def_FatkhullinPolyak_Flow_GradientFlow

namespace FatkhullinPolyak.Flow

open Matrix

theorem flow_energy_identity {n m r : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ) (C : Matrix (Fin r) (Fin n) ℝ)
    (Q : Matrix (Fin n) (Fin n) ℝ) (R : Matrix (Fin m) (Fin m) ℝ) (Sig : Matrix (Fin n) (Fin n) ℝ)
    (hQ : Q.PosDef) (hR : R.PosDef) (hSig : Sig.PosDef)
    (K₀ : Matrix (Fin m) (Fin r) ℝ) (K : ℝ → Matrix (Fin m) (Fin r) ℝ)
    (hK : IsGradFlow A B C Q R Sig K₀ K) :
    ∀ t : ℝ, 0 ≤ t →
      HasDerivWithinAt (fun s => cost A B C Q R Sig (K s))
        (-(frobNorm (grad A B C Q R Sig (K t)) ^ 2)) (Set.Ici 0) t := by sorry

end FatkhullinPolyak.Flow
