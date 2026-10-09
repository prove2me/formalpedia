-- Prove2me | Theorems.Thm_CertDRO_Conc_eq_4_strong_concavity
-- name    : CertDRO.Conc.eq_4_strong_concavity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T19:09:29.707162+00:00
-- url     : https://prove2.me/theorems/4cc20362-a1d0-444e-9844-34e894308862
-- title:
--   (4) — the penalized inner problem z ↦ ℓ(θ; z) − γc(z, z₀) is (γ − L_zz)-strongly concave
-- statement:
--   Let $Z\subseteq\mathbb R^m$ be convex, fix $\theta\in\mathbb R^d$ and $z_0\in\mathbb R^m$, and let $\ell(\theta;\cdot)$ have gradient $g_z(\theta,z)$ at every $z\in Z$ with
--   $$\|g_z(\theta,z)-g_z(\theta,z')\|_2\le L_{zz}\|z-z'\|_2\qquad(z,z'\in Z).$$
--   Suppose $z\mapsto c(z,z_0)$ is $1$-strongly convex on $Z$. If $\gamma\ge L_{zz}$, then
--   $$z\longmapsto \ell(\theta;z)-\gamma\,c(z,z_0)\quad\text{is }(\gamma-L_{zz})\text{-strongly concave on }Z .$$
--
--   This is the insight behind the whole paper: for a large enough penalty the inner maximization defining the transportation map is a strongly concave problem, so its maximizer is unique and stable.
--
--   **Formalization Note** The paper phrases the conclusion through the first-order condition (4), which involves $\nabla_z c$; the Lean statement asserts strong concavity directly (Mathlib's `StrongConcaveOn Z (γ - Lzz)`), so $c$ need not be differentiable. The norm is $\ell_2$.
-- source:
--   Sinha, Namkoong, Volpi, Duchi, Certifying Some Distributional Robustness with Principled Adversarial Training, arXiv:1710.10571v5, p. 4, §2, (4) and the following sentence

import Definitions.Def_CertDRO_Conc_model

namespace CertDRO.Conc

/-- §2, (4) and the following sentence, p. 4: if `∇_z ℓ(θ; ·)` is `Lzz`-Lipschitz on the convex set
`Z` and `c(·, z₀)` is `1`-strongly convex on `Z`, then for `γ ≥ Lzz` the map
`z ↦ ℓ(θ; z) − γ c(z, z₀)` is `(γ − Lzz)`-strongly concave on `Z`. -/
theorem eq_4_strong_concavity {d m : ℕ} (Z : Set (CertDRO.SGD.Data m)) (hZ : Convex ℝ Z)
    (ℓ : CertDRO.SGD.Param d → CertDRO.SGD.Data m → ℝ) (gz : CertDRO.SGD.Param d → CertDRO.SGD.Data m → CertDRO.SGD.Data m) (c : CertDRO.SGD.Data m → CertDRO.SGD.Data m → ℝ)
    (θ : CertDRO.SGD.Param d) (z₀ : CertDRO.SGD.Data m) (Lzz γ : ℝ)
    (hgrad : ∀ z ∈ Z, HasGradientAt (fun z' => ℓ θ z') (gz θ z) z)
    (hlip : ∀ z ∈ Z, ∀ z' ∈ Z, ‖gz θ z - gz θ z'‖ ≤ Lzz * ‖z - z'‖)
    (hc : StrongConvexOn Z 1 (fun z => c z z₀))
    (hγ : Lzz ≤ γ) :
    StrongConcaveOn Z (γ - Lzz) (fun z => ℓ θ z - γ * c z z₀) := by sorry

end CertDRO.Conc
