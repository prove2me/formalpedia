-- Prove2me | Theorems.Thm_CertDRO_SGD_delta_bound
-- name    : CertDRO.SGD.delta_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T18:19:43.136818+00:00
-- url     : https://prove2.me/theorems/aac0c31e-2f4b-473e-9292-5e746804701c
-- title:
--   §B.3 — the gradient bias of an ε-approximate maximizer: ‖δ‖² ≤ 2L_θz² ε/(γ − L_zz)
-- statement:
--   Assume the standing hypotheses ($Z$ nonempty, convex and closed; Assumptions A and B for the Euclidean norm; $\gamma>L_{zz}$). Let $z_0\in Z$, $\epsilon\in\mathbb R$, and let $\hat z\in Z$ be an $\epsilon$-approximate maximizer of $z\mapsto\ell(\theta;z)-\gamma c(z,z_0)$, i.e. $\ell(\theta;\hat z)-\gamma c(\hat z,z_0)\ge\varphi_\gamma(\theta;z_0)-\epsilon$. Then the error $\delta=\nabla_\theta\ell(\theta;\hat z)-\nabla_\theta\varphi_\gamma(\theta;z_0)$ satisfies
--   $$\|\delta\|_2^2\le\frac{2L_{\theta z}^2}{\gamma-L_{zz}}\,\epsilon .$$
--
--   The bound shows that an inexact inner maximization costs a bias of order $\epsilon$ in the stochastic gradient, independent of the step and of $T$.
--
--   **Formalization Note** The gradient $\nabla_\theta\varphi_\gamma(\theta;z_0)$ is Mathlib's `gradient` of $\theta'\mapsto\varphi_\gamma(\theta';z_0)$ at $\theta$. The maximizer $z_\star$ of the paper's display does not appear in the statement.
-- source:
--   Sinha, Namkoong, Volpi, Duchi, Certifying Some Distributional Robustness with Principled Adversarial Training, arXiv:1710.10571v5, p. 41, §B.3, first display

import Definitions.Def_CertDRO_SGD_model

namespace CertDRO.SGD

/-- §B.3, first display of p. 41: under the standing hypotheses (`γ > Lzz`), if `ẑ` is an
`ε`-approximate maximizer of `ℓ(θ; ·) − γ c(·, z₀)` over `Z` (with `z₀ ∈ Z`), then the gradient error
`δ = ∇_θ ℓ(θ; ẑ) − ∇_θ φ_γ(θ; z₀)` satisfies `‖δ‖² ≤ (2 Lθz² / (γ − Lzz)) ε`. -/
theorem delta_bound {d m : ℕ} (Z : Set (Data m)) (c : Data m → Data m → ℝ)
    (ℓ : Param d → Data m → ℝ) (gθ : Param d → Data m → Param d) (gz : Param d → Data m → Data m)
    (Lθθ Lzz Lθz Lzθ γ : ℝ)
    (hS : Standing Z c ℓ gθ gz Lθθ Lzz Lθz Lzθ γ)
    (ε : ℝ) (θ : Param d) (z₀ zh : Data m) (hz₀ : z₀ ∈ Z)
    (hzh : IsApproxMaximizer Z ℓ c γ ε θ z₀ zh) :
    ‖gradient (fun θ' => robustSurrogate Z ℓ c γ θ' z₀) θ - gθ θ zh‖ ^ 2 ≤
      2 * Lθz ^ 2 / (γ - Lzz) * ε := by sorry

end CertDRO.SGD
