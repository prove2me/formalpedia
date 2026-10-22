-- Prove2me | Theorems.Thm_AbelianLieExt_Integrability_lemma_IV_2
-- name    : AbelianLieExt.Integrability.lemma_IV_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T09:28:18.009312+00:00
-- url     : https://prove2.me/theorems/43d27e43-506a-4914-90fc-6808c4a04259
-- title:
--   Lemma IV.2, p. 15 — the period group Π_ω is fixed pointwise by G
-- statement:
--   Let $G$ be a connected real Banach–Lie group with Lie algebra $\mathfrak g$, let $A$ be a smooth $G$-module with $A_0 \cong \mathfrak a/\Gamma_A$ via $q_A\colon \mathfrak a \to A$, and let $\omega \in Z^2_c(\mathfrak g, \mathfrak a)$ be a continuous Lie algebra 2-cocycle. Write $\rho_{\mathfrak a}$ for the induced action of $G$ on $\mathfrak a$ and $\Pi_\omega \subseteq \mathfrak a$ for the period group of $\omega$, the set of integrals $\int_\sigma \omega^{\mathrm{eq}}$ of the equivariant 2-form over smooth spheres $\sigma$ in $G$. Then
--
--   $$\Pi_\omega \subseteq \mathfrak a^G, \qquad\text{i.e.}\qquad \rho_{\mathfrak a}(g)\,v = v \quad\text{for all } v \in \Pi_\omega,\ g \in G.$$
--
--   This is the first structural fact about the period group: it lies in the fixed points of $G$, so the condition $\Pi_\omega \subseteq \Gamma_A$ of the integrability criterion only involves the $G$-invariant part of $\mathfrak a$.
--
--   **Formalization Note** Real Banach scope (see the Setting definition). The paper only needs $\mathfrak a$ to be a smooth $G$-module; the statement here is phrased through a module $A$ with $A_0 \cong \mathfrak a/\Gamma_A$, which loses nothing because $A := \mathfrak a$, $q_A := \mathrm{id}$ is such a module. $\Pi_\omega$ is encoded by smooth spheres $\mathbb R^2 \to G$ equal to $1$ off the open unit square, which represent every class of $\pi_2(G)$.
-- source:
--   Neeb, Abelian extensions of infinite-dimensional Lie groups, arXiv:math/0402303v1, p. 15, Lemma IV.2

import Mathlib
import Definitions.Def_AbelianLieExt_Integrability_Setting

open scoped Manifold

namespace AbelianLieExt.Integrability

/-- Lemma IV.2, arXiv:math/0402303v1, p. 15: the period group is fixed pointwise by `G`. -/
theorem lemma_IV_2
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {G : Type} [TopologicalSpace G] [ChartedSpace E G] [Group G] [LieGroup 𝓘(ℝ, E) (⊤ : ℕ∞) G]
    {a : Type} [NormedAddCommGroup a] [NormedSpace ℝ a] [CompleteSpace a]
    {A : Type} [TopologicalSpace A] [ChartedSpace a A] [AddCommGroup A]
    [LieAddGroup 𝓘(ℝ, a) (⊤ : ℕ∞) A] [DistribMulAction G A]
    [ConnectedSpace G] (qA : a →+ A) (hA : IsSmoothModuleCover (E := E) (G := G) A qA)
    (ω : LieAlg E G →L[ℝ] LieAlg E G →L[ℝ] a) (hω : IsCocycle2 A ω) :
    ∀ v ∈ periodSet A ω, ∀ g : G, rhoA A g v = v := by sorry

end AbelianLieExt.Integrability
