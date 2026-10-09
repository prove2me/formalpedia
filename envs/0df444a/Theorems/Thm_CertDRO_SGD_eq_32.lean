-- Prove2me | Theorems.Thm_CertDRO_SGD_eq_32
-- name    : CertDRO.SGD.eq_32
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T18:19:32.952762+00:00
-- url     : https://prove2.me/theorems/d8e22f71-b54d-4ce1-9d61-5c7e1ca9e22f
-- title:
--   (32) — the one-step bound with the bias δ = g − ∇_θφ_γ separated, for α ≤ 1/L_φ
-- statement:
--   Let $F:\mathbb R^d\to\mathbb R$ be differentiable with $L_\varphi$-Lipschitz gradient, $L_\varphi\ge0$, and let $0\le\alpha$ with $L_\varphi\alpha\le1$. For all $\theta,g,u\in\mathbb R^d$, writing $\delta=g-u$,
--   $$F(\theta-\alpha g)\le F(\theta)-\frac\alpha2\|\nabla F(\theta)\|_2^2+\alpha(1-L_\varphi\alpha)\langle\nabla F(\theta),\nabla F(\theta)-u\rangle+\frac{\alpha(1+L_\varphi\alpha)}2\|\delta\|_2^2+L_\varphi\alpha^2\|u-\nabla F(\theta)\|_2^2 .$$
--
--   In the proof of Theorem 2, $u=\nabla_\theta\varphi_\gamma(\theta^t;z^t)$ is the exact stochastic gradient and $\delta^t=g^t-u$ is the bias caused by solving the inner maximization only approximately; the inequality separates a mean-zero term, the bias and the variance.
--
--   **Formalization Note** The paper assumes $\alpha_t\le1/L_\varphi$ "in the rest of the proof" (p. 40); this is the hypothesis $L_\varphi\alpha\le1$ together with $\alpha\ge0$ and $L_\varphi\ge0$, which the step $\pm\langle a,b\rangle\le\frac12\|a\|^2+\frac12\|b\|^2$ needs.
-- source:
--   Sinha, Namkoong, Volpi, Duchi, Certifying Some Distributional Robustness with Principled Adversarial Training, arXiv:1710.10571v5, p. 40, §B.3, (32)

import Definitions.Def_CertDRO_SGD_model

namespace CertDRO.SGD

/-- (32), §B.3, p. 40: for a differentiable `F` on `ℝ^d` with `L_φ`-Lipschitz gradient (`L_φ ≥ 0`) and a
stepsize `0 ≤ α ≤ 1/L_φ`, the step `θ⁺ = θ − α g` satisfies, for every vector `u` (in the proof,
`u = ∇_θ φ_γ(θ^t; z^t)`) and with `δ = g − u`,
`F(θ⁺) ≤ F(θ) − (α/2)‖∇F(θ)‖² + α(1 − L_φ α)⟨∇F(θ), ∇F(θ) − u⟩ + (α(1 + L_φ α)/2)‖δ‖²
  + L_φ α² ‖u − ∇F(θ)‖²`. -/
theorem eq_32 {d : ℕ} (F : Param d → ℝ) (Lφ : ℝ) (hF : Differentiable ℝ F)
    (hL : ∀ θ θ', ‖gradient F θ - gradient F θ'‖ ≤ Lφ * ‖θ - θ'‖) (hLφ : 0 ≤ Lφ)
    (θ g u : Param d) (α : ℝ) (hα : 0 ≤ α) (hαL : Lφ * α ≤ 1) :
    F (θ - α • g) ≤ F θ - α / 2 * ‖gradient F θ‖ ^ 2
      + α * (1 - Lφ * α) * inner ℝ (gradient F θ) (gradient F θ - u)
      + α * (1 + Lφ * α) / 2 * ‖g - u‖ ^ 2
      + Lφ * α ^ 2 * ‖u - gradient F θ‖ ^ 2 := by sorry

end CertDRO.SGD
