-- Prove2me | Theorems.Thm_CertDRO_Conc_lemma_5
-- name    : CertDRO.Conc.lemma_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T19:09:46.976302+00:00
-- url     : https://prove2.me/theorems/9570ce61-3445-45bb-9a1c-a969971fa81f
-- title:
--   Lemma 5 — |c(T(θ₁; z), z) − c(T(θ₂; z), z)| ≤ L_cL_zθ/(γ − L_zz) ‖θ₁ − θ₂‖
-- statement:
--   Let $Z\subseteq\mathbb R^m$ be convex and $\Theta\subseteq\mathbb R^d$. Let $c$ satisfy Assumption A, let $\ell$ satisfy Assumption B on $\Theta\times Z$ with constants $L_{\theta\theta},L_{zz},L_{\theta z},L_{z\theta}$, let $\gamma>L_{zz}$, and let $T$ be a transportation map on $\Theta$. Assume one of the two cases of Theorem 4, with a constant $L_c\ge0$:
--   1. (i) $c$ is $L_c$-Lipschitz over $Z$ in each argument; or
--   2. (ii) for every $\theta\in\Theta$, $\ell(\theta;z)\in[0,M_\ell]$ for $z\in Z$ and $z\mapsto\ell(\theta;z)$ is $\gamma L_c$-Lipschitz on $Z$.
--
--   Then for every $z\in Z$ and all $\theta_1,\theta_2\in\Theta$,
--   $$|c(T(\theta_1;z),z)-c(T(\theta_2;z),z)|\le\frac{L_cL_{z\theta}}{\gamma-L_{zz}}\,\|\theta_1-\theta_2\|_2 .$$
--
--   The lemma converts the Lipschitz continuity of the transportation map into Lipschitz continuity of the transported cost, the quantity whose average is the robustness level.
--
--   **Formalization Note** $[\gamma-L_{zz}]_+$ is $\gamma-L_{zz}$ under $\gamma>L_{zz}$. The bound $\|z\|\le M_z$ of Theorem 4 is not needed for this lemma and is omitted. The norm is $\ell_2$.
-- source:
--   Sinha, Namkoong, Volpi, Duchi, Certifying Some Distributional Robustness with Principled Adversarial Training, arXiv:1710.10571v5, p. 43, §B.7, Lemma 5

import Definitions.Def_CertDRO_Conc_model

namespace CertDRO.Conc

/-- Lemma 5, p. 43: under the conditions of Theorem 4 (Assumptions A and B, `γ > Lzz`, and case (i)
or case (ii) on `Θ`), for every `z ∈ Z` and all `θ₁, θ₂ ∈ Θ`,
`|c(T(θ₁; z), z) − c(T(θ₂; z), z)| ≤ Lc Lzθ / (γ − Lzz) · ‖θ₁ − θ₂‖`. -/
theorem lemma_5 {d m : ℕ} (Z : Set (CertDRO.SGD.Data m)) (hZ : Convex ℝ Z) (Θ : Set (CertDRO.SGD.Param d))
    (ℓ : CertDRO.SGD.Param d → CertDRO.SGD.Data m → ℝ) (gθ : CertDRO.SGD.Param d → CertDRO.SGD.Data m → CertDRO.SGD.Param d)
    (gz : CertDRO.SGD.Param d → CertDRO.SGD.Data m → CertDRO.SGD.Data m) (c : CertDRO.SGD.Data m → CertDRO.SGD.Data m → ℝ) (T : CertDRO.SGD.Param d → CertDRO.SGD.Data m → CertDRO.SGD.Data m)
    (Lθθ Lzz Lθz Lzθ γ Lc Mℓ : ℝ)
    (hA : CertDRO.SGD.AssumptionA Z c) (hB : AssumptionB Θ Z ℓ gθ gz Lθθ Lzz Lθz Lzθ)
    (hγ : Lzz < γ) (hT : IsTransportMap Θ Z ℓ c γ T)
    (hcase : CaseI Z c Lc ∨ CaseII Θ Z ℓ γ Lc Mℓ) :
    ∀ z ∈ Z, ∀ θ₁ ∈ Θ, ∀ θ₂ ∈ Θ,
      |c (T θ₁ z) z - c (T θ₂ z) z| ≤ Lc * Lzθ / (γ - Lzz) * ‖θ₁ - θ₂‖ := by sorry

end CertDRO.Conc
