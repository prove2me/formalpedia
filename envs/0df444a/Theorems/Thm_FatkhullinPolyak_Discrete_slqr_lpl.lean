-- Prove2me | Theorems.Thm_FatkhullinPolyak_Discrete_slqr_lpl
-- name    : FatkhullinPolyak.Discrete.slqr_lpl
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T12:41:36.389789+00:00
-- url     : https://prove2.me/theorems/69569bdb-af41-48be-9d7f-591b236fd4f5
-- title:
--   Theorem 3.17 — state-feedback LQR satisfies the LPL condition on $\mathcal S_0$ with the explicit $\mu$ of (3.11)
-- statement:
--   Consider state feedback, $C=I$, with $Q,R,\Sigma\succ0$ and $B\ne0$. Let $K_0\in\mathcal S$ and let $K_*\in\mathcal S$ be an optimal gain. Define
--   $$\mu=\frac{\lambda_1(R)\,\lambda_1^2(\Sigma)\,\lambda_1(Q)}{8f(K_*)\Big(\|A\|+\frac{\|B\|^2f_S(K_0)}{\lambda_1(\Sigma)\lambda_1(R)}\Big)^2}, \tag{3.11}$$
--   with $\|\cdot\|$ the spectral norm. Then $\mu>0$ and $f_S$ satisfies the Łežanski–Polyak–Łojasiewicz (LPL) condition on $\mathcal S_0$:
--   $$\tfrac12\|\nabla f_S(K)\|_F^2\ge\mu\big(f_S(K)-f_S(K_*)\big)\qquad\text{for all }K\in\mathcal S_0. \tag{3.10}$$
--
--   Gradient domination replaces convexity, which $f_S$ lacks; together with $L$-smoothness on $\mathcal S_0$ it yields the linear convergence of the gradient method to $K_*$ (Theorem 4.2).
-- source:
--   Fatkhullin, Polyak, Optimizing Static Linear Feedback: Gradient Method, arXiv:2004.09875v2, p. 10, Theorem 3.17, (3.10)–(3.11)

import Mathlib
import Definitions.Def_FatkhullinPolyak_Discrete_LQR

open Filter Topology

namespace FatkhullinPolyak.Discrete

/-- Theorem 3.17 (p. 10): for state feedback `C = I`, `f_S` satisfies the LPL condition on `S₀`,
(3.10) `½‖∇f_S(K)‖_F² ≥ µ (f_S(K) − f_S(K⋆))`, with `µ > 0` given by (3.11)
`µ = λ₁(R)λ₁²(Σ)λ₁(Q) / (8 f(K⋆) (‖A‖ + ‖B‖² f_S(K₀) / (λ₁(Σ)λ₁(R)))²)`. -/
theorem slqr_lpl {n m : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (Q : Matrix (Fin n) (Fin n) ℝ) (R : Matrix (Fin m) (Fin m) ℝ)
    (Sig : Matrix (Fin n) (Fin n) ℝ)
    (hQ : Q.PosDef) (hR : R.PosDef) (hSig : Sig.PosDef) (hB : B ≠ 0)
    (K₀ Kstar : Matrix (Fin m) (Fin n) ℝ) (hK₀ : K₀ ∈ stabSet A B (1 : Matrix (Fin n) (Fin n) ℝ))
    (hKstar : Kstar ∈ stabSet A B (1 : Matrix (Fin n) (Fin n) ℝ))
    (hopt : ∀ K' ∈ stabSet A B (1 : Matrix (Fin n) (Fin n) ℝ), lqrCost A B (1 : Matrix (Fin n) (Fin n) ℝ) Q R Sig Kstar ≤ lqrCost A B (1 : Matrix (Fin n) (Fin n) ℝ) Q R Sig K') :
    let μ : ℝ := lamMin R * lamMin Sig ^ 2 * lamMin Q /
      (8 * lqrCost A B (1 : Matrix (Fin n) (Fin n) ℝ) Q R Sig Kstar *
        (specNorm A + specNorm B ^ 2 * lqrCost A B (1 : Matrix (Fin n) (Fin n) ℝ) Q R Sig K₀ / (lamMin Sig * lamMin R)) ^ 2)
    0 < μ ∧ ∀ K ∈ sublevel A B (1 : Matrix (Fin n) (Fin n) ℝ) Q R Sig K₀,
      μ * (lqrCost A B (1 : Matrix (Fin n) (Fin n) ℝ) Q R Sig K - lqrCost A B (1 : Matrix (Fin n) (Fin n) ℝ) Q R Sig Kstar) ≤
        (1 / 2) * frobNorm (lqrGrad A B (1 : Matrix (Fin n) (Fin n) ℝ) Q R Sig K) ^ 2 := by sorry

end FatkhullinPolyak.Discrete
