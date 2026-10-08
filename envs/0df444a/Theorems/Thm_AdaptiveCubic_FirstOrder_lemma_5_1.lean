-- Prove2me | Theorems.Thm_AdaptiveCubic_FirstOrder_lemma_5_1
-- name    : AdaptiveCubic.FirstOrder.lemma_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:38:22.006973+00:00
-- url     : https://prove2.me/theorems/1589fbf9-78c7-4801-b994-09052b829c06
-- title:
--   Lemma 5.1 — σ_k stays below L₀ = max(σ₀, (3/2)γ₂(C + L))
-- statement:
--   Let $f\in C^2(\mathbb R^n)$ (AF.3) with Hessian $H=\nabla^2 f$, and assume
--
--   1. AF.6: $\|H(x)-H(y)\|\le L\|x-y\|$ for all $x,y\in\mathbb R^n$, with $L>0$;
--   2. AM.4: $\|(H(x_k)-B_k)s_k\|\le C\|s_k\|^2$ for all $k\ge0$, with $C>0$.
--
--   Then along every run of ARC (Algorithm 2.1) satisfying (2.6), $m_k(s_k)<f(x_k)$ for all $k$,
--
--   $$\sigma_k\le\max\!\left(\sigma_0,\ \tfrac32\gamma_2(C+L)\right)=:L_0\quad\text{for all }k\ge0.$$
--
--   The regularisation weight cannot grow without bound: once $\sigma_k$ is large the cubic term dominates the Taylor error, the iteration is very successful, and $\sigma$ stops increasing. The bound $L_0$ enters the constant $\kappa_g$ of Lemma 5.2 and, through Theorem 2.1, the count of unsuccessful iterations.
--
--   **Formalization Note** The page states the lemma for the basic ARC framework and for ARC(S) "as long as (2.6) holds" (p. 13); it is stated here for any ARC run, with (2.6) for all $k$ as an explicit hypothesis. The Hessian is `fderiv ℝ (gradient f)`, and its norm is the operator norm.
-- source:
--   Cartis, Gould & Toint, Adaptive cubic regularisation methods for unconstrained optimization. Part II, preprint rev. 15 Sep 2009 (UNamur), p. 13, Lemma 5.1, (5.4) (= Part I, Lemma 5.2); p. 12, AF.3 (5.1), AF.6 (5.2), AM.4 (5.3)

import Mathlib
import Definitions.Def_AdaptiveCubic_Cauchy_IsARCRun

open scoped RealInnerProductSpace

namespace AdaptiveCubic.FirstOrder

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

end AdaptiveCubic.FirstOrder
