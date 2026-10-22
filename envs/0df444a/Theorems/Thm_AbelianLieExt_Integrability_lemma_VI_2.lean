-- Prove2me | Theorems.Thm_AbelianLieExt_Integrability_lemma_VI_2
-- name    : AbelianLieExt.Integrability.lemma_VI_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T09:28:18.441502+00:00
-- url     : https://prove2.me/theorems/deb19842-f184-46b6-b751-8870e9d0a80d
-- title:
--   Lemma VI.2 (first assertion, (1), (2)), p. 22 — the path flux F̃_ω(γ): linear, a cocycle on closed loops, homotopy invariant mod B¹_c
-- statement:
--   Let $G$ be a connected real Banach–Lie group with Lie algebra $\mathfrak g$, $A$ a smooth $G$-module with $A_0 \cong \mathfrak a/\Gamma_A$, and $\omega \in Z^2_c(\mathfrak g, \mathfrak a)$. For a smooth curve $\gamma$ in $G$ define
--
--   $$\widetilde F_\omega(\gamma)(x) = \int_0^1 \gamma(t).\omega\big(\gamma(t)^{-1}\gamma'(t),\ \mathrm{Ad}(\gamma(t))^{-1}.x\big)\,dt, \qquad x \in \mathfrak g.$$
--
--   Then:
--
--   1. $\widetilde F_\omega(\gamma)\colon \mathfrak g \to \mathfrak a$ is a continuous linear map;
--   2. if $\gamma(1)^{-1}\gamma(0)$ lies in the centre $Z(G)$ and acts trivially on $\mathfrak a$, then $\widetilde F_\omega(\gamma) \in Z^1_c(\mathfrak g, \mathfrak a)$;
--   3. if $\gamma_1$ and $\gamma_2$ have the same endpoints and are homotopic with fixed endpoints on $[0,1]$, then $\widetilde F_\omega(\gamma_1) - \widetilde F_\omega(\gamma_2)$ is a coboundary.
--
--   These properties make the flux of a loop a well-defined class in $H^1_c(\mathfrak g, \mathfrak a)$ that depends only on the homotopy class of the loop.
--
--   **Formalization Note** Real Banach scope (see the Setting definition). Curves are smooth maps $\mathbb R \to G$ restricted to $[0,1]$ rather than piecewise smooth paths on $[0,1]$; every piecewise smooth path can be reparametrised monotonically into a smooth one with the same flux. Part (3) of the lemma (the integral of $\widetilde F_\omega(\gamma)^{\mathrm{eq}}$ along a curve) is not formalized; it is used only for Corollary VI.5.
-- source:
--   Neeb, Abelian extensions of infinite-dimensional Lie groups, arXiv:math/0402303v1, p. 22, Lemma VI.2 (first assertion, (1), (2))

import Mathlib
import Definitions.Def_AbelianLieExt_Integrability_Setting

open scoped Manifold

namespace AbelianLieExt.Integrability

/-- Lemma VI.2 (first assertion, (1) and (2)), arXiv:math/0402303v1, p. 22. -/
theorem lemma_VI_2
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {G : Type} [TopologicalSpace G] [ChartedSpace E G] [Group G] [LieGroup 𝓘(ℝ, E) (⊤ : ℕ∞) G]
    {a : Type} [NormedAddCommGroup a] [NormedSpace ℝ a] [CompleteSpace a]
    {A : Type} [TopologicalSpace A] [ChartedSpace a A] [AddCommGroup A]
    [LieAddGroup 𝓘(ℝ, a) (⊤ : ℕ∞) A] [DistribMulAction G A]
    [ConnectedSpace G] (qA : a →+ A) (hA : IsSmoothModuleCover (E := E) (G := G) A qA)
    (ω : LieAlg E G →L[ℝ] LieAlg E G →L[ℝ] a) (hω : IsCocycle2 A ω) :
    -- `F̃_ω(γ)` is a continuous linear map `𝔤 → 𝔞`
    (∀ γ : ℝ → G, ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (⊤ : ℕ∞) γ →
      ∃ L : LieAlg E G →L[ℝ] a, ∀ x, L x = fluxCocycle A ω γ x) ∧
    -- (1)
    (∀ γ : ℝ → G, ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (⊤ : ℕ∞) γ →
      (γ 1)⁻¹ * γ 0 ∈ Subgroup.center G → (∀ v : a, rhoA A ((γ 1)⁻¹ * γ 0) v = v) →
      IsCocycle1 A (fluxCocycle A ω γ)) ∧
    -- (2)
    (∀ (x y : G) (γ₁ γ₂ : ℝ → G) (p₁ p₂ : Path x y),
      ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (⊤ : ℕ∞) γ₁ → ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (⊤ : ℕ∞) γ₂ →
      (∀ t : unitInterval, p₁ t = γ₁ (t : ℝ)) → (∀ t : unitInterval, p₂ t = γ₂ (t : ℝ)) →
      p₁.Homotopic p₂ →
      IsCoboundary1 A (fun z => fluxCocycle A ω γ₁ z - fluxCocycle A ω γ₂ z)) := by sorry

end AbelianLieExt.Integrability
