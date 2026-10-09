-- Prove2me | Theorems.Thm_ExtraConsensus_Linear_eq_3_35
-- name    : ExtraConsensus.Linear.eq_3_35
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T09:15:36.703+00:00
-- url     : https://prove2.me/theorems/8ff28126-8eac-4d69-8d1f-cf88a6bd3d8f
-- title:
--   Eq. (3.35), p. 16 — ‖q^{k+1} − q*‖²_F ≤ θ(σmax(I+W−2W̃)+αL_f)²/λ̃min(W̃−W)‖x^{k+1} − x*‖²_F + θ(σmax(W̃)+αL_f)²/((θ−1)λ̃min(W̃−W))‖x^k − x^{k+1}‖²_F
-- statement:
--   Under Assumptions 1–3, with $U=(\tilde W-W)^{1/2}$ and $\alpha>0$, let $x^*$ solve (1.1), $\mathbf x^*=\mathbf 1(x^*)^{\mathsf T}$, and let $\mathbf q^*=U\mathbf p$ satisfy (3.1)–(3.2) with $\mathbf x^*$. Let $\sigma_{\max}(\cdot)$ be the largest singular value and $\tilde\lambda_{\min}(\tilde W-W)$ the smallest nonzero eigenvalue of $\tilde W-W$. Then for every $\theta>1$ and every $k$
--   $$
--   \|\mathbf q^{k+1}-\mathbf q^*\|_F^2\le\frac{\theta\big(\sigma_{\max}(I+W-2\tilde W)+\alpha L_{\mathbf f}\big)^2}{\tilde\lambda_{\min}(\tilde W-W)}\|\mathbf x^{k+1}-\mathbf x^*\|_F^2+\frac{\theta\big(\sigma_{\max}(\tilde W)+\alpha L_{\mathbf f}\big)^2}{(\theta-1)\tilde\lambda_{\min}(\tilde W-W)}\|\mathbf x^k-\mathbf x^{k+1}\|_F^2 .
--   $$
--   On the page, $\theta$ comes from the inequality $\|\mathbf a+\mathbf b+\mathbf c+\mathbf d\|_F^2\le\theta\big(\frac{\beta}{\beta-1}\|\mathbf a\|_F^2+\beta\|\mathbf b\|_F^2\big)+\frac{\theta}{\theta-1}\big(\frac{\gamma}{\gamma-1}\|\mathbf c\|_F^2+\gamma\|\mathbf d\|_F^2\big)$, "which holds for any $\theta>1$, $\beta>1$, $\gamma>1$". The bound controls the dual error $\mathbf q^{k+1}-\mathbf q^*$ by primal quantities, which is what lets the $\mathbf q$-part of $\|\mathbf z^{k+1}-\mathbf z^*\|_G^2$ be absorbed in Theorem 3.7.
--
--   **Formalization Note** The extreme singular values and $\tilde\lambda_{\min}$ are pinned by their characterisations, not bounded. The statement assumes neither $L_{\mathbf f}>0$ nor $\sigma_{\max}(I+W-2\tilde W)>0$: the page's choice $\beta=1+\sigma_{\max}(I+W-2\tilde W)/(\alpha L_{\mathbf f})$, $\gamma=1+\sigma_{\max}(\tilde W)/(\alpha L_{\mathbf f})$ needs both, but (3.35) itself holds without them (directly from the triangle inequality). Since $\tilde\lambda_{\min}$ exists only for $\tilde W\ne W$, the hypotheses force $n\ge2$.
-- source:
--   Shi, Ling, Wu & Yin, arXiv:1404.6264v4, proof of Theorem 3.7, eq. (3.35), p. 16 (θ > 1 from (3.33))

import Mathlib
import Definitions.Def_ExtraConsensus_Linear_Model

namespace ExtraConsensus.Linear

open Matrix

/-- Shi–Ling–Wu–Yin, arXiv:1404.6264v4, eq. (3.35), p. 16 (proof of Theorem 3.7): for every `θ > 1`
and every `k`, `‖𝐪^{k+1} − 𝐪*‖²_F ≤ θ(σmax(I+W−2W̃)+αL_𝐟)²/λ̃min(W̃−W) ‖𝐱^{k+1} − 𝐱*‖²_F
  + θ(σmax(W̃)+αL_𝐟)²/((θ−1)λ̃min(W̃−W)) ‖𝐱ᵏ − 𝐱^{k+1}‖²_F`.
The extreme singular values and the smallest nonzero eigenvalue are pinned by their characterisations. -/
theorem eq_3_35 {n p : ℕ} (hn : 0 < n) (Gr : SimpleGraph (Fin n))
    (W Wt U : Matrix (Fin n) (Fin n) ℝ) (f : Fin n → EuclideanSpace ℝ (Fin p) → ℝ) (Lf α : ℝ)
    (hA1 : MixingAssumption Gr W Wt) (hA2 : ExtraConsensus.Sublinear.ConvexLipschitzGrad f Lf) (hA3 : ExtraConsensus.Sublinear.SolutionExists f)
    (hUs : Uᵀ = U) (hUpsd : U.PosSemidef) (hU2 : U * U = Wt - W)
    (hα0 : 0 < α)
    (xs : EuclideanSpace ℝ (Fin p)) (hsol : ∀ y, ExtraConsensus.Sublinear.fbar f xs ≤ ExtraConsensus.Sublinear.fbar f y)
    (qs : ExtraConsensus.Sublinear.Stack n p) (hopt : ExtraConsensus.Sublinear.IsOptimalPair U α f qs (fun _ => xs))
    (s1 : ℝ) (hs1 : IsSigmaMax (1 + W - (2 : ℝ) • Wt) s1)
    (s2 : ℝ) (hs2 : IsSigmaMax Wt s2)
    (lt : ℝ) (hlt : IsLamMinNZ (Wt - W) lt)
    (θ : ℝ) (hθ : 1 < θ) (x0 : ExtraConsensus.Sublinear.Stack n p) :
    let x := ExtraConsensus.Sublinear.extraIter α W Wt f x0
    let q := ExtraConsensus.Sublinear.qSeq U x
    let Xs : ExtraConsensus.Sublinear.Stack n p := fun _ => xs
    ∀ k : ℕ,
      ExtraConsensus.Sublinear.frob (q (k + 1) - qs) (q (k + 1) - qs)
        ≤ θ * (s1 + α * Lf) ^ 2 / lt * ExtraConsensus.Sublinear.frob (x (k + 1) - Xs) (x (k + 1) - Xs)
          + θ * (s2 + α * Lf) ^ 2 / ((θ - 1) * lt) * ExtraConsensus.Sublinear.frob (x k - x (k + 1)) (x k - x (k + 1)) := by sorry

end ExtraConsensus.Linear
