-- Prove2me | Theorems.Thm_CertDRO_Conc_eq_16_transport_lipschitz
-- name    : CertDRO.Conc.eq_16_transport_lipschitz
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T19:09:33.083969+00:00
-- url     : https://prove2.me/theorems/be9a212d-1819-42f7-bf42-1d8bd527ec2b
-- title:
--   (16) — the transport map satisfies ‖T(θ₁; z) − T(θ₂; z)‖ ≤ L_zθ/(γ − L_zz) ‖θ₁ − θ₂‖
-- statement:
--   Let $Z\subseteq\mathbb R^m$ be convex and $\Theta\subseteq\mathbb R^d$, let the cost $c$ satisfy Assumption A and the loss $\ell$ satisfy Assumption B on $\Theta\times Z$ with constants $L_{\theta\theta},L_{zz},L_{\theta z},L_{z\theta}$, and let $\gamma>L_{zz}$. Let $T$ be a transportation map, $T(\theta;z_0)\in\operatorname{argmax}_{z\in Z}\{\ell(\theta;z)-\gamma c(z,z_0)\}$ for all $\theta\in\Theta$ and $z_0\in Z$. Then for every $z\in Z$ and all $\theta_1,\theta_2\in\Theta$,
--   $$\|T(\theta_1;z)-T(\theta_2;z)\|_2\le\frac{L_{z\theta}}{\gamma-L_{zz}}\,\|\theta_1-\theta_2\|_2 .$$
--
--   This smoothness of the worst-case perturbation in the parameter is the starting point of the uniform concentration argument for the robustness level.
--
--   **Formalization Note** The paper writes $[\gamma-L_{zz}]_+$; under the hypothesis $\gamma>L_{zz}$ (p. 43: "our strong concavity assumption that $\gamma>L_{zz}$") this is $\gamma-L_{zz}$. The norm is $\ell_2$ on both spaces.
-- source:
--   Sinha, Namkoong, Volpi, Duchi, Certifying Some Distributional Robustness with Principled Adversarial Training, arXiv:1710.10571v5, p. 10, §3.2, (16)

import Definitions.Def_CertDRO_Conc_model

namespace CertDRO.Conc

/-- §3.2, (16), p. 10: under Assumptions A and B on `Θ × Z` with `γ > Lzz`, the transportation map
is Lipschitz in the parameter: for every `z ∈ Z` and all `θ₁, θ₂ ∈ Θ`,
`‖T(θ₁; z) − T(θ₂; z)‖ ≤ Lzθ / (γ − Lzz) · ‖θ₁ − θ₂‖`. -/
theorem eq_16_transport_lipschitz {d m : ℕ} (Z : Set (CertDRO.SGD.Data m)) (hZ : Convex ℝ Z)
    (Θ : Set (CertDRO.SGD.Param d))
    (ℓ : CertDRO.SGD.Param d → CertDRO.SGD.Data m → ℝ) (gθ : CertDRO.SGD.Param d → CertDRO.SGD.Data m → CertDRO.SGD.Param d)
    (gz : CertDRO.SGD.Param d → CertDRO.SGD.Data m → CertDRO.SGD.Data m) (c : CertDRO.SGD.Data m → CertDRO.SGD.Data m → ℝ) (T : CertDRO.SGD.Param d → CertDRO.SGD.Data m → CertDRO.SGD.Data m)
    (Lθθ Lzz Lθz Lzθ γ : ℝ)
    (hA : CertDRO.SGD.AssumptionA Z c) (hB : AssumptionB Θ Z ℓ gθ gz Lθθ Lzz Lθz Lzθ)
    (hγ : Lzz < γ) (hT : IsTransportMap Θ Z ℓ c γ T) :
    ∀ z ∈ Z, ∀ θ₁ ∈ Θ, ∀ θ₂ ∈ Θ, ‖T θ₁ z - T θ₂ z‖ ≤ Lzθ / (γ - Lzz) * ‖θ₁ - θ₂‖ := by sorry

end CertDRO.Conc
