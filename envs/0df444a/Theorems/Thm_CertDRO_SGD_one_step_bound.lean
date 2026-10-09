-- Prove2me | Theorems.Thm_CertDRO_SGD_one_step_bound
-- name    : CertDRO.SGD.one_step_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T18:19:43.565208+00:00
-- url     : https://prove2.me/theorems/c1363c07-afff-4fef-9c26-1e299da05136
-- title:
--   §B.3 — one step of Algorithm 1 in conditional expectation
-- statement:
--   Assume the standing hypotheses ($Z$ nonempty, convex and closed; Assumptions A and B for the Euclidean norm; $\gamma>L_{zz}$). Let $P_0$ be a probability measure on $\mathbb R^m$ with $P_0(Z)=1$, such that $\varphi_\gamma(\theta;\cdot)$ is $P_0$-integrable for every $\theta$, and let $F(\theta)=\mathbb E_{P_0}[\varphi_\gamma(\theta;Z)]$. Let $\epsilon\ge0$ and let $\hat z(\theta,z_0)$ be a jointly measurable $\epsilon$-approximate maximization oracle. Assume for every $\theta$
--   $$\mathbb E_{P_0}\|\nabla F(\theta)-\nabla_\theta\varphi_\gamma(\theta;Z)\|_2^2\le\sigma^2 .$$
--   Fix $\theta$, a stepsize $\alpha>0$ with $L_\varphi\alpha\le1$, and set $\theta^+(z)=\theta-\alpha\nabla_\theta\ell(\theta;\hat z(\theta,z))$, the next iterate of Algorithm 1 when the fresh sample is $z\sim P_0$. Then $z\mapsto F(\theta^+(z))$ and $z\mapsto\|\nabla_\theta\varphi_\gamma(\theta;z)-\nabla F(\theta)\|_2^2$ are $P_0$-integrable, and
--   $$\mathbb E_{z\sim P_0}[F(\theta^+(z))]-F(\theta)\le-\frac\alpha2\|\nabla F(\theta)\|_2^2+\alpha\hat\epsilon+L_\varphi\alpha^2\,\mathbb E_{z\sim P_0}\|\nabla_\theta\varphi_\gamma(\theta;z)-\nabla F(\theta)\|_2^2,\qquad\hat\epsilon=\frac{2L_{\theta z}^2}{\gamma-L_{zz}}\epsilon .$$
--
--   This is the conditional expectation of (32) given $\theta^t=\theta$, combined with the bias bound; summing it over the run gives Theorem 2.
--
--   **Formalization Note** The conditional expectation given $\theta^t$ is written as the integral over the fresh sample with $\theta$ fixed (the sample $z^t$ is independent of $\theta^t$). The paper prints the last term without the expectation and with $\theta$ for $\theta^t$; the statement uses the expectation. Integrability of the two integrands is part of the conclusion. The variance hypothesis is a lower Lebesgue integral, so it is not satisfied vacuously by a non-integrable integrand; joint measurability of the oracle and $\epsilon\ge0$ are implicit in the paper.
-- source:
--   Sinha, Namkoong, Volpi, Duchi, Certifying Some Distributional Robustness with Principled Adversarial Training, arXiv:1710.10571v5, p. 41, §B.3, second display

import Definitions.Def_CertDRO_SGD_model

namespace CertDRO.SGD

open MeasureTheory

/-- §B.3, second display of p. 41 (one step of Algorithm 1 in conditional expectation): fix the current
iterate `θ` and draw a fresh sample `z ∼ P₀`. Under the hypotheses of Theorem 2, for a stepsize
`0 < α ≤ 1/L_φ` the next iterate `θ⁺ = θ − α ∇_θ ℓ(θ; ẑ(θ, z))` satisfies
`E[F(θ⁺)] − F(θ) ≤ −(α/2)‖∇F(θ)‖² + α ε̂ + L_φ α² E‖∇_θ φ_γ(θ; z) − ∇F(θ)‖²`,
with `ε̂ = 2 Lθz² ε / (γ − Lzz)`; both expectations are of integrable functions. -/
theorem one_step_bound {d m : ℕ} (Z : Set (Data m)) (c : Data m → Data m → ℝ)
    (ℓ : Param d → Data m → ℝ) (gθ : Param d → Data m → Param d) (gz : Param d → Data m → Data m)
    (Lθθ Lzz Lθz Lzθ γ : ℝ)
    (hS : Standing Z c ℓ gθ gz Lθθ Lzz Lθz Lzθ γ)
    (P₀ : Measure (Data m)) [IsProbabilityMeasure P₀] (hP₀ : P₀ Zᶜ = 0)
    (hint : ∀ θ, Integrable (fun z => robustSurrogate Z ℓ c γ θ z) P₀)
    (ε : ℝ) (hε : 0 ≤ ε) (zhat : Param d → Data m → Data m)
    (hzhat : IsOracle Z ℓ c γ ε zhat) (hzhat_meas : Measurable (Function.uncurry zhat))
    (σ : ℝ)
    (hvar : ∀ θ, ∫⁻ z, ENNReal.ofReal (‖gradient (robustObjective Z ℓ c γ P₀) θ -
        gradient (fun θ' => robustSurrogate Z ℓ c γ θ' z) θ‖ ^ 2) ∂P₀ ≤ ENNReal.ofReal (σ ^ 2))
    (θ : Param d) (α : ℝ) (hα : 0 < α) (hαL : Lphi Lθθ Lzz Lθz Lzθ γ * α ≤ 1) :
    Integrable (fun z => robustObjective Z ℓ c γ P₀ (θ - α • gθ θ (zhat θ z))) P₀ ∧
    Integrable (fun z => ‖gradient (fun θ' => robustSurrogate Z ℓ c γ θ' z) θ -
        gradient (robustObjective Z ℓ c γ P₀) θ‖ ^ 2) P₀ ∧
    (∫ z, robustObjective Z ℓ c γ P₀ (θ - α • gθ θ (zhat θ z)) ∂P₀) -
        robustObjective Z ℓ c γ P₀ θ ≤
      -(α / 2) * ‖gradient (robustObjective Z ℓ c γ P₀) θ‖ ^ 2
        + α * (2 * Lθz ^ 2 / (γ - Lzz) * ε)
        + Lphi Lθθ Lzz Lθz Lzθ γ * α ^ 2 *
          ∫ z, ‖gradient (fun θ' => robustSurrogate Z ℓ c γ θ' z) θ -
            gradient (robustObjective Z ℓ c γ P₀) θ‖ ^ 2 ∂P₀ := by sorry

end CertDRO.SGD
