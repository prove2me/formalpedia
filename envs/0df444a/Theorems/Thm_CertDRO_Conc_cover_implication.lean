-- Prove2me | Theorems.Thm_CertDRO_Conc_cover_implication
-- name    : CertDRO.Conc.cover_implication
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T19:09:32.504353+00:00
-- url     : https://prove2.me/theorems/e2d77414-fa35-4e7e-b6ce-6df3111d482f
-- title:
--   §B.7 — a (γ − L_zz)t/(4L_cL_zθ)-cover of Θ turns |g| ≤ t/2 at the centres into sup_Θ |g| ≤ t
-- statement:
--   Let $\Theta\subseteq\mathbb R^d$, let $L_{zz}<\gamma$, $L_c>0$, $L_{z\theta}>0$ and $t>0$, and put
--   $$r=\frac{(\gamma-L_{zz})\,t}{4L_cL_{z\theta}},\qquad L=\frac{2L_cL_{z\theta}}{\gamma-L_{zz}} .$$
--   Let $S\supseteq\Theta$ and let $\{\theta_1,\dots,\theta_N\}\subseteq S$ be a finite $r$-cover of $\Theta$ in the Euclidean norm (every $\theta\in\Theta$ has some $\theta_i$ with $\|\theta-\theta_i\|_2\le r$), and let $g:\mathbb R^d\to\mathbb R$ satisfy $|g(\theta)-g(\theta')|\le L\|\theta-\theta'\|_2$ for all $\theta,\theta'\in S$. If $|g(\theta_i)|\le t/2$ for every $i$, then
--   $$\sup_{\theta\in\Theta}|g(\theta)|\le t .$$
--
--   In the proof of Theorem 4 this is applied to the deviation $g=\widehat\rho_n-\rho$ of the empirical from the population robustness level; it reduces the uniform bound to finitely many fixed-parameter bounds.
--
--   **Formalization Note** The set $S$ carries both the centres and the Lipschitz property: $S=\Theta$ is a cover by points of $\Theta$ (the one the goal uses), $S=\mathbb R^d$ a cover with centres anywhere. The supremum is a real supremum; for $\Theta=\emptyset$ it is $0$ and the conclusion holds since $t>0$.
-- source:
--   Sinha, Namkoong, Volpi, Duchi, Certifying Some Distributional Robustness with Principled Adversarial Training, arXiv:1710.10571v5, p. 44, §B.7, second and third sentences after the proof of Lemma 5

import Definitions.Def_CertDRO_Conc_model

namespace CertDRO.Conc

/-- §B.7, p. 44, the covering step: let `C = {θ₁, …, θ_N}` be a `(γ − Lzz) t / (4 Lc Lzθ)`-cover of
`Θ` whose centres lie in a set `S ⊇ Θ`, and let `g` be `2 Lc Lzθ / (γ − Lzz)`-Lipschitz on `S`. If
`|g(θᵢ)| ≤ t/2` at every centre, then `sup_{θ ∈ Θ} |g(θ)| ≤ t`. (`S = Θ` is the internal cover used
by the goal; `S = ℝ^d` allows centres anywhere.) -/
theorem cover_implication {d : ℕ} (Θ S : Set (CertDRO.SGD.Param d)) (C : Finset (CertDRO.SGD.Param d))
    (g : CertDRO.SGD.Param d → ℝ)
    (Lzz Lzθ γ Lc t : ℝ) (hγ : Lzz < γ) (hLc : 0 < Lc) (hLzθ : 0 < Lzθ) (ht : 0 < t)
    (hΘS : Θ ⊆ S) (hCS : ∀ x ∈ C, x ∈ S)
    (hcover : Θ ⊆ ⋃ x ∈ C, Metric.closedBall x ((γ - Lzz) * t / (4 * Lc * Lzθ)))
    (hg : ∀ θ₁ ∈ S, ∀ θ₂ ∈ S, |g θ₁ - g θ₂| ≤ 2 * Lc * Lzθ / (γ - Lzz) * ‖θ₁ - θ₂‖)
    (hC : ∀ θ ∈ C, |g θ| ≤ t / 2) :
    ⨆ θ : Θ, |g θ| ≤ t := by sorry

end CertDRO.Conc
