-- Prove2me | Theorems.Thm_CertDRO_SGD_eq_4_strong_concavity
-- name    : CertDRO.SGD.eq_4_strong_concavity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T18:19:33.805717+00:00
-- url     : https://prove2.me/theorems/343893bd-9a6b-4b21-b8ac-a315b5d777d7
-- title:
--   (4) — for γ ≥ L, z ↦ ℓ(θ; z) − γc(z, z₀) is (γ − L)-strongly concave
-- statement:
--   Let $Z\subseteq\mathbb R^m$ be convex, fix $\theta$ and $z_0$, and suppose $z\mapsto\ell(\theta;z)$ has gradient $\nabla_z\ell(\theta;z)$ at every $z\in Z$ which is $L$-Lipschitz on $Z$:
--   $$\|\nabla_z\ell(\theta;z)-\nabla_z\ell(\theta;z')\|_2\le L\|z-z'\|_2\qquad(z,z'\in Z).$$
--   Suppose $z\mapsto c(z,z_0)$ is $1$-strongly convex on $Z$ with respect to $\|\cdot\|_2$. If $\gamma\ge L$, then
--   $$z\longmapsto \ell(\theta;z)-\gamma c(z,z_0)\quad\text{is } (\gamma-L)\text{-strongly concave on } Z .$$
--
--   This is the observation that makes the inner maximization of the robust surrogate a strongly concave problem whenever the penalty $\gamma$ dominates the smoothness of the loss in $z$.
--
--   **Formalization Note** The paper derives this from the Taylor expansion (4), which differentiates $c$; the statement here is the conclusion of the sentence following (4) and does not require $c(\cdot,z_0)$ to be differentiable. The cost is real valued (the paper allows the value $+\infty$ at this point). The Euclidean norm is used throughout.
-- source:
--   Sinha, Namkoong, Volpi, Duchi, Certifying Some Distributional Robustness with Principled Adversarial Training, arXiv:1710.10571v5, p. 4, §2, (4) and the following sentence

import Definitions.Def_CertDRO_SGD_model

namespace CertDRO.SGD

/-- §2, (4) and the following sentence, p. 4: if `∇_z ℓ(θ; ·)` is `L`-Lipschitz on the convex set `Z`
and `c(·, z₀)` is `1`-strongly convex on `Z`, then for `γ ≥ L` the map `z ↦ ℓ(θ; z) − γ c(z, z₀)` is
`(γ − L)`-strongly concave on `Z`. -/
theorem eq_4_strong_concavity {d m : ℕ} (Z : Set (Data m)) (hZ : Convex ℝ Z)
    (ℓ : Param d → Data m → ℝ) (gz : Param d → Data m → Data m) (c : Data m → Data m → ℝ)
    (θ : Param d) (z₀ : Data m) (L γ : ℝ)
    (hgrad : ∀ z ∈ Z, HasGradientAt (fun z' => ℓ θ z') (gz θ z) z)
    (hlip : ∀ z ∈ Z, ∀ z' ∈ Z, ‖gz θ z - gz θ z'‖ ≤ L * ‖z - z'‖)
    (hc : StrongConvexOn Z 1 (fun z => c z z₀))
    (hγ : L ≤ γ) :
    StrongConcaveOn Z (γ - L) (fun z => ℓ θ z - γ * c z z₀) := by sorry

end CertDRO.SGD
