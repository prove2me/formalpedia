-- Prove2me | Theorems.Thm_CertDRO_SGD_lemma_1
-- name    : CertDRO.SGD.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T18:19:37.780979+00:00
-- url     : https://prove2.me/theorems/c2d17999-9411-47f3-87fb-893c28fe25d6
-- title:
--   Lemma 1 — the supremum of a strongly concave family is smooth, with a Lipschitz maximizer
-- statement:
--   Let $Z\subseteq\mathbb R^m$ be nonempty and convex, and let $f:\mathbb R^d\times\mathbb R^m\to\mathbb R$ have partial gradients $g_\theta=\nabla_\theta f$ and $g_z=\nabla_z f$ satisfying Assumption B (with $f$ in place of $\ell$) for the Euclidean norm. Let $\lambda>0$ and suppose $z\mapsto f(\theta,z)$ is $\lambda$-strongly concave on $Z$ for every $\theta$. Define
--   $$\bar f(\theta)=\sup_{z\in Z}f(\theta,z),$$
--   and let $z_\star(\theta)\in Z$ be a maximizer of $f(\theta,\cdot)$ over $Z$ for every $\theta$. Then:
--
--   1. $\bar f$ is differentiable with $\nabla\bar f(\theta)=g_\theta(\theta,z_\star(\theta))$ for every $\theta$;
--   2. $\|z_\star(\theta_1)-z_\star(\theta_2)\|_2\le \dfrac{L_{z\theta}}{\lambda}\|\theta_1-\theta_2\|_2$ for all $\theta_1,\theta_2$;
--   3. $$\|\nabla\bar f(\theta)-\nabla\bar f(\theta')\|_2\le\Big(L_{\theta\theta}+\frac{L_{\theta z}L_{z\theta}}{\lambda}\Big)\|\theta-\theta'\|_2 .$$
--
--   The lemma transfers smoothness of $f$ to the value function $\bar f$; it is applied to the penalized loss to show that the robust surrogate has Lipschitz gradients.
--
--   **Formalization Note** The paper states the lemma for a general norm and its dual; here both $\Theta=\mathbb R^d$ and $\mathbb R^m$ carry the Euclidean norm, the case used by Theorem 2. The maximizer $z_\star$ is a hypothesis tied to $f$ by the argmax property; it is unique by strong concavity. Only partial gradients are assumed, in place of joint differentiability of $f$.
-- source:
--   Sinha, Namkoong, Volpi, Duchi, Certifying Some Distributional Robustness with Principled Adversarial Training, arXiv:1710.10571v5, p. 5, Lemma 1 (proof in §B.2, pp. 39–40)

import Definitions.Def_CertDRO_SGD_model

namespace CertDRO.SGD

/-- Lemma 1, p. 5 (ℓ²-norm on `Θ = ℝ^d` and on `ℝ^m`): if `f(θ, ·)` is `λ`-strongly concave on the convex
set `Z` for every `θ`, its partial gradients satisfy Assumption B, and `z⋆(θ)` maximizes `f(θ, ·)` over
`Z`, then `f̄(θ) = sup_{z ∈ Z} f(θ, z)` is differentiable with `∇f̄(θ) = gθ(θ, z⋆(θ))`, `z⋆` is
`(Lzθ/λ)`-Lipschitz, and `∇f̄` is `(Lθθ + Lθz Lzθ/λ)`-Lipschitz. -/
theorem lemma_1 {d m : ℕ} (Z : Set (Data m)) (hZne : Z.Nonempty) (hZ : Convex ℝ Z)
    (f : Param d → Data m → ℝ) (gθ : Param d → Data m → Param d) (gz : Param d → Data m → Data m)
    (Lθθ Lzz Lθz Lzθ lam : ℝ)
    (hB : AssumptionB Z f gθ gz Lθθ Lzz Lθz Lzθ) (hlam : 0 < lam)
    (hconc : ∀ θ, StrongConcaveOn Z lam (f θ))
    (zstar : Param d → Data m)
    (hzstar : ∀ θ, zstar θ ∈ Z ∧ ∀ z ∈ Z, f θ z ≤ f θ (zstar θ)) :
    (∀ θ, HasGradientAt (supOver Z f) (gθ θ (zstar θ)) θ) ∧
    (∀ θ₁ θ₂, ‖zstar θ₁ - zstar θ₂‖ ≤ Lzθ / lam * ‖θ₁ - θ₂‖) ∧
    (∀ θ θ', ‖gradient (supOver Z f) θ - gradient (supOver Z f) θ'‖ ≤
      (Lθθ + Lθz * Lzθ / lam) * ‖θ - θ'‖) := by sorry

end CertDRO.SGD
