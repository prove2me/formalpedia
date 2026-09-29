-- Prove2me | Theorems.Thm_FatkhullinPolyak_Flow_flow_integral_bound
-- name    : FatkhullinPolyak.Flow.flow_integral_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T12:47:12.990452+00:00
-- url     : https://prove2.me/theorems/76e9879e-5e40-4d4a-9652-d545ebdb20a9
-- title:
--   Appendix D.1 — $f(K_0)\ge f(K_0)-f(K_T)=\int_0^T\|\nabla f(K_t)\|^2dt\ge T\min_{0\le t\le T}\|\nabla f(K_t)\|^2$
-- statement:
--   Let $Q, R, \Sigma\succ0$ and let $K_t$ be a solution on $[0,\infty)$ of the gradient flow (4.1). Then for every $T\ge0$:
--
--   1. $f(K_0) \ge f(K_0) - f(K_T)$;
--   2. $f(K_0) - f(K_T) = \displaystyle\int_0^T \|\nabla f(K_t)\|_F^2\,dt$;
--   3. there is $t\in[0,T]$ with $T\,\|\nabla f(K_t)\|_F^2 \le \displaystyle\int_0^T\|\nabla f(K_s)\|_F^2\,ds$.
--
--   Together,
--   $$f(K_0) \;\ge\; f(K_0)-f(K_T) \;=\; \int_0^T\|\nabla f(K_t)\|_F^2\,dt \;\ge\; T\min_{0\le t\le T}\|\nabla f(K_t)\|_F^2 ,$$
--   which is the chain from which the estimate (4.2) follows.
--
--   **Formalization Note** The minimum over $[0,T]$ is rendered as the existence of a point $t\in[0,T]$ at which the bound holds (the minimum of a continuous function on a compact interval is attained). The integral is the interval integral from $0$ to $T$.
-- source:
--   Fatkhullin, Polyak, Optimizing Static Linear Feedback: Gradient Method, arXiv:2004.09875v2, p. 18, Appendix D.1, display

import Mathlib
import Definitions.Def_FatkhullinPolyak_Flow_LQR
import Definitions.Def_FatkhullinPolyak_Flow_GradientFlow

namespace FatkhullinPolyak.Flow

open Matrix

theorem flow_integral_bound {n m r : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ) (C : Matrix (Fin r) (Fin n) ℝ)
    (Q : Matrix (Fin n) (Fin n) ℝ) (R : Matrix (Fin m) (Fin m) ℝ) (Sig : Matrix (Fin n) (Fin n) ℝ)
    (hQ : Q.PosDef) (hR : R.PosDef) (hSig : Sig.PosDef)
    (K₀ : Matrix (Fin m) (Fin r) ℝ) (K : ℝ → Matrix (Fin m) (Fin r) ℝ)
    (hK : IsGradFlow A B C Q R Sig K₀ K) (T : ℝ) (hT : 0 ≤ T) :
    cost A B C Q R Sig K₀ - cost A B C Q R Sig (K T) ≤ cost A B C Q R Sig K₀ ∧
      cost A B C Q R Sig K₀ - cost A B C Q R Sig (K T) =
        ∫ t in (0 : ℝ)..T, frobNorm (grad A B C Q R Sig (K t)) ^ 2 ∧
      ∃ t ∈ Set.Icc (0 : ℝ) T,
        T * frobNorm (grad A B C Q R Sig (K t)) ^ 2 ≤
          ∫ s in (0 : ℝ)..T, frobNorm (grad A B C Q R Sig (K s)) ^ 2 := by sorry

end FatkhullinPolyak.Flow
