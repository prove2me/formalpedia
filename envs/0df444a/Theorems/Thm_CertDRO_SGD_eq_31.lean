-- Prove2me | Theorems.Thm_CertDRO_SGD_eq_31
-- name    : CertDRO.SGD.eq_31
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T18:19:46.568963+00:00
-- url     : https://prove2.me/theorems/fc0f30d0-475a-4bf6-956a-9aa42d5390c9
-- title:
--   (31) — the descent inequality for an L_φ-smooth objective along θ − αg
-- statement:
--   Let $F:\mathbb R^d\to\mathbb R$ be differentiable with $L_\varphi$-Lipschitz gradient, $\|\nabla F(\theta)-\nabla F(\theta')\|_2\le L_\varphi\|\theta-\theta'\|_2$. Then for every $\theta, g\in\mathbb R^d$ and every $\alpha\in\mathbb R$,
--   $$F(\theta-\alpha g)\le F(\theta)-\alpha\Big(1-\tfrac12L_\varphi\alpha\Big)\|\nabla F(\theta)\|_2^2+\alpha(1-L_\varphi\alpha)\langle\nabla F(\theta),\nabla F(\theta)-g\rangle+\frac{L_\varphi\alpha^2}{2}\|g-\nabla F(\theta)\|_2^2 .$$
--
--   In the proof of Theorem 2 this is applied with $\theta=\theta^t$, $g=g^t=\nabla_\theta\ell(\theta^t;\hat z^t)$ and $\alpha=\alpha_t$, so that the left side is $F(\theta^{t+1})$; it is the progress guarantee of one step of Algorithm 1.
--
--   **Formalization Note** The statement is deterministic and holds for any stepsize; the paper's displayed chain of equalities after the first inequality is algebra.
-- source:
--   Sinha, Namkoong, Volpi, Duchi, Certifying Some Distributional Robustness with Principled Adversarial Training, arXiv:1710.10571v5, p. 40, §B.3, (31)

import Definitions.Def_CertDRO_SGD_model

namespace CertDRO.SGD

/-- (31), §B.3, p. 40: for a differentiable `F` on `ℝ^d` with `L_φ`-Lipschitz gradient, the step
`θ⁺ = θ − α g` satisfies
`F(θ⁺) ≤ F(θ) − α(1 − ½ L_φ α)‖∇F(θ)‖² + α(1 − L_φ α)⟨∇F(θ), ∇F(θ) − g⟩ + (L_φ α²/2)‖g − ∇F(θ)‖²`. -/
theorem eq_31 {d : ℕ} (F : Param d → ℝ) (Lφ : ℝ) (hF : Differentiable ℝ F)
    (hL : ∀ θ θ', ‖gradient F θ - gradient F θ'‖ ≤ Lφ * ‖θ - θ'‖)
    (θ g : Param d) (α : ℝ) :
    F (θ - α • g) ≤ F θ - α * (1 - 1 / 2 * Lφ * α) * ‖gradient F θ‖ ^ 2
      + α * (1 - Lφ * α) * inner ℝ (gradient F θ) (gradient F θ - g)
      + Lφ * α ^ 2 / 2 * ‖g - gradient F θ‖ ^ 2 := by sorry

end CertDRO.SGD
