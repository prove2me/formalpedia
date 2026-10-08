-- Prove2me | Theorems.Thm_AdaptiveCubic_SecondOrder_lemma_5_1
-- name    : AdaptiveCubic.SecondOrder.lemma_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:38:25.733611+00:00
-- url     : https://prove2.me/theorems/a3f52c56-29d1-486a-8543-3e71fee828e0
-- title:
--   Lemma 5.1 — σ_k ≤ L₀ = max(σ₀, (3/2)γ₂(C + L))
-- statement:
--   Consider a run of the ARC algorithm on $f$ with $m_k(s_k)<f(x_k)$ for all $k$ (2.6). Assume
--
--   1. **AF.3**: $f\in C^2(\mathbb R^n)$, with Hessian $H(x)=\nabla^2 f(x)$;
--   2. **AF.6**: $\|H(x)-H(y)\|\le L\|x-y\|$ for all $x,y\in\mathbb R^n$, for some $L>0$;
--   3. **AM.4**: $\|(H(x_k)-B_k)s_k\|\le C\|s_k\|^2$ for all $k\ge0$, for some $C>0$.
--
--   Then
--
--   $$\sigma_k\le \max\Big(\sigma_0,\ \tfrac32\gamma_2(C+L)\Big) =: L_0 \qquad\text{for all } k\ge0. \qquad (5.4)$$
--
--   Once $\sigma_k$ exceeds a multiple of the Lipschitz constants the iteration is very successful and $\sigma_k$ stops growing, so the weights stay bounded. This bound feeds Theorem 2.1 and the step-length estimates for ARC(S).
--
--   **Formalization Note** $H$ is `fderiv ℝ (gradient f)` and the norm on operators is the operator norm. The page states the lemma "as long as (2.6) holds" (p. 13); (2.6) is an explicit hypothesis for all $k$. The lemma does not use the ARC(S) step conditions, only the ARC run.
-- source:
--   Cartis, Gould & Toint, Adaptive cubic regularisation methods for unconstrained optimization. Part II, preprint rev. 15 Sep 2009 (UNamur), p. 13, Lemma 5.1, (5.4); p. 12, AF.3 (5.1), AF.6 (5.2), AM.4 (5.3)

import Mathlib
import Definitions.Def_AdaptiveCubic_Cauchy_IsARCRun

open scoped RealInnerProductSpace

namespace AdaptiveCubic.SecondOrder

/-- Lemma 5.1, p. 13 (Cartis, Gould & Toint, ARC Part II, preprint rev. 15 Sep 2009; = Part I,
Lemma 5.2). Let AF.3 (`f ∈ C²(ℝⁿ)`, (5.1)), AF.6 (`‖H(x) − H(y)‖ ≤ L‖x − y‖` for all `x, y`,
`L > 0`, (5.2)) and AM.4 (`‖(H(x_k) − B_k)s_k‖ ≤ C‖s_k‖²` for all `k`, `C > 0`, (5.3)) hold,
where `H = ∇²f` is `fderiv ℝ (gradient f)`. Then along every run of ARC,
`σ_k ≤ max(σ₀, (3/2)γ₂(C + L)) =: L₀` for all `k` (5.4).
The page applies the lemma "as long as (2.6) holds" (p. 13); (2.6), `m_k(s_k) < f(x_k)` for all
`k`, is a hypothesis. -/
theorem lemma_5_1 {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (γ₁ γ₂ η₁ η₂ : ℝ)
    (x s : ℕ → EuclideanSpace ℝ (Fin n)) (σ : ℕ → ℝ)
    (B : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hrun : AdaptiveCubic.Cauchy.IsARCRun f γ₁ γ₂ η₁ η₂ x s σ B)
    (hAF3 : ContDiff ℝ 2 f)
    (L : ℝ) (hL : 0 < L)
    (hAF6 : ∀ y z, ‖fderiv ℝ (gradient f) y - fderiv ℝ (gradient f) z‖ ≤ L * ‖y - z‖)
    (C : ℝ) (hC : 0 < C)
    (hAM4 : ∀ k, ‖(fderiv ℝ (gradient f) (x k) - B k) (s k)‖ ≤ C * ‖s k‖ ^ 2)
    (h26 : ∀ k, AdaptiveCubic.Cauchy.model f (B k) (σ k) (x k) (s k) < f (x k)) :
    ∀ k, σ k ≤ max (σ 0) (3 / 2 * γ₂ * (C + L)) := by sorry

end AdaptiveCubic.SecondOrder
