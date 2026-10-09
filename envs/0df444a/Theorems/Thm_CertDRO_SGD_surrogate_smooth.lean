-- Prove2me | Theorems.Thm_CertDRO_SGD_surrogate_smooth
-- name    : CertDRO.SGD.surrogate_smooth
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T18:19:32.424242+00:00
-- url     : https://prove2.me/theorems/d9589b9b-5317-46b4-924e-165761262005
-- title:
--   §2.1 — φ_γ(·; z₀) has L_φ-Lipschitz gradient ∇_θφ_γ(θ; z₀) = ∇_θℓ(θ; z⋆(z₀, θ))
-- statement:
--   Assume the standing hypotheses: $Z\subseteq\mathbb R^m$ is nonempty, convex and closed, the cost $c$ satisfies Assumption A and the loss $\ell$ satisfies Assumption B for the Euclidean norm, and $\gamma>L_{zz}$. Fix $z_0\in Z$ and let $z_\star(z_0,\theta)\in Z$ maximize $z\mapsto\ell(\theta;z)-\gamma c(z,z_0)$ over $Z$ for every $\theta$. Then the robust surrogate $\varphi_\gamma(\cdot;z_0)$ is differentiable with
--   $$\nabla_\theta\varphi_\gamma(\theta;z_0)=\nabla_\theta\ell(\theta;z_\star(z_0,\theta)),$$
--   and its gradient is Lipschitz:
--   $$\|\nabla_\theta\varphi_\gamma(\theta;z_0)-\nabla_\theta\varphi_\gamma(\theta';z_0)\|_2\le L_\varphi\|\theta-\theta'\|_2,\qquad L_\varphi=L_{\theta\theta}+\frac{L_{\theta z}L_{z\theta}}{\gamma-L_{zz}} .$$
--
--   This is Lemma 1 applied to $f(\theta,z)=\ell(\theta;z)-\gamma c(z,z_0)$, which is $(\gamma-L_{zz})$-strongly concave in $z$ by (4). It identifies the update direction of Algorithm 1 and makes the objective $F$ an $L_\varphi$-smooth function.
--
--   **Formalization Note** The paper writes $[\gamma-L_{zz}]_+$; the hypothesis $\gamma>L_{zz}$ makes this the positive number $\gamma-L_{zz}$. The cost $c(\cdot,z_0)$ is not assumed differentiable. $Z$ is assumed closed (so maximizers exist); the maximizer map is a hypothesis tied to its objective.
-- source:
--   Sinha, Namkoong, Volpi, Duchi, Certifying Some Distributional Robustness with Principled Adversarial Training, arXiv:1710.10571v5, p. 6, §2.1, paragraph after Algorithm 1

import Definitions.Def_CertDRO_SGD_model

namespace CertDRO.SGD

/-- §2.1, paragraph after Algorithm 1, p. 6: under Assumptions A and B (ℓ²-norm) with `γ > Lzz`, for
every `z₀ ∈ Z` the robust surrogate `φ_γ(·; z₀)` is differentiable with
`∇_θ φ_γ(θ; z₀) = ∇_θ ℓ(θ; z⋆(z₀, θ))`, where `z⋆(z₀, θ)` maximizes `ℓ(θ; ·) − γ c(·, z₀)` over `Z`,
and its gradient is `L_φ`-Lipschitz with `L_φ = Lθθ + Lθz Lzθ / (γ − Lzz)`. -/
theorem surrogate_smooth {d m : ℕ} (Z : Set (Data m)) (c : Data m → Data m → ℝ)
    (ℓ : Param d → Data m → ℝ) (gθ : Param d → Data m → Param d) (gz : Param d → Data m → Data m)
    (Lθθ Lzz Lθz Lzθ γ : ℝ)
    (hS : Standing Z c ℓ gθ gz Lθθ Lzz Lθz Lzθ γ)
    (z₀ : Data m) (hz₀ : z₀ ∈ Z)
    (zstar : Param d → Data m) (hzstar : ∀ θ, IsMaximizer Z ℓ c γ θ z₀ (zstar θ)) :
    (∀ θ, HasGradientAt (fun θ' => robustSurrogate Z ℓ c γ θ' z₀) (gθ θ (zstar θ)) θ) ∧
    (∀ θ θ', ‖gradient (fun θ' => robustSurrogate Z ℓ c γ θ' z₀) θ -
        gradient (fun θ' => robustSurrogate Z ℓ c γ θ' z₀) θ'‖ ≤
      Lphi Lθθ Lzz Lθz Lzθ γ * ‖θ - θ'‖) := by sorry

end CertDRO.SGD
