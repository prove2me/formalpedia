-- Prove2me | Theorems.Thm_AbelianLieExt_Integrability_theorem_VI_7
-- name    : AbelianLieExt.Integrability.theorem_VI_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T09:28:18.122016+00:00
-- url     : https://prove2.me/theorems/62f97f2c-d0cc-4aac-bffd-e8ea57837ea1
-- title:
--   Theorem VI.7, p. 27 — Integrability Criterion: 𝔞 ⊕_ω 𝔤 integrates to A ↪ Ĝ ↠ G with Ĝ connected iff Π_ω ⊆ Γ_A and F_ω = θ̄_A ∘ γ for a surjective γ
-- statement:
--   **Integrability Criterion.** Let $G$ be a connected real Banach–Lie group with Lie algebra $\mathfrak g$, and let $A$ be a smooth $G$-module with $A_0 \cong \mathfrak a/\Gamma_A$, where $\Gamma_A$ is a discrete subgroup of the Banach space $\mathfrak a$. For each continuous 2-cocycle $\omega \in Z^2_c(\mathfrak g, \mathfrak a)$, the abelian Lie algebra extension $\mathfrak a \hookrightarrow \widehat{\mathfrak g} := \mathfrak a \oplus_\omega \mathfrak g \twoheadrightarrow \mathfrak g$ integrates to a Lie group extension $A \hookrightarrow \widehat G \twoheadrightarrow G$ with a connected Lie group $\widehat G$ if and only if
--
--   1. $\Pi_\omega \subseteq \Gamma_A$, and
--   2. there exists a surjective homomorphism $\gamma\colon \pi_1(G) \to \pi_0(A)$ such that the flux homomorphism $F_\omega\colon \pi_1(G) \to H^1_c(\mathfrak g, \mathfrak a)$ and the characteristic homomorphism $\overline\theta_A\colon \pi_0(A) \to H^1_c(\mathfrak g, \mathfrak a)$ are related by
--   $$F_\omega = \overline\theta_A \circ \gamma.$$
--
--   If $A$ is connected, then (2) is equivalent to $F_\omega = 0$.
--
--   This is the central result of the paper: it reduces the integrability of an abelian Lie algebra extension to two computable obstructions, the period group $\Pi_\omega$ (a homomorphism out of $\pi_2(G)$) and the flux homomorphism $F_\omega$ (out of $\pi_1(G)$).
--
--   **Formalization Note** The paper works over $\mathbb K \in \{\mathbb R, \mathbb C\}$ with sequentially complete locally convex model spaces; here $G$, $A$ and $\widehat G$ are real Lie groups modelled on Banach spaces (a special case), smooth means $C^\infty$, and all types live in `Type`. $A_0 \cong \mathfrak a/\Gamma_A$ is given by a smooth equivariant homomorphism $q_A$ which is a local diffeomorphism with derivative $\mathrm{id}$ at $0$ and image $A_0$; $\Gamma_A = \ker q_A$. "Integrates" is the existence of an actual Lie group extension (`IntegratesToConnected`): $\widehat G$ with smooth $\iota\colon A \hookrightarrow \widehat G$ and surjective $q\colon \widehat G \to G$, $\ker q = \iota(A)$, a smooth local trivialisation, the prescribed conjugation action, and a Lie algebra isomorphism with $\mathfrak a \oplus_\omega \mathfrak g$ compatible with $\mathrm d\iota$ and $\mathrm dq$. $\pi_0(A)$ is $A/q_A(\mathfrak a)$, $\pi_1(G)$ is Mathlib's fundamental group at $1$, and $F_\omega$, $\overline\theta_A$ are compared on smooth loop representatives modulo coboundaries. The paper writes $\mathfrak a \times_\omega \mathfrak g$ for $\mathfrak a \oplus_\omega \mathfrak g$.
-- source:
--   Neeb, Abelian extensions of infinite-dimensional Lie groups, arXiv:math/0402303v1, p. 27, Theorem VI.7 (Integrability Criterion)

import Mathlib
import Definitions.Def_AbelianLieExt_Integrability_Setting

open scoped Manifold

namespace AbelianLieExt.Integrability

/-- Theorem VI.7 (Integrability Criterion), arXiv:math/0402303v1, p. 27. -/
theorem theorem_VI_7
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {G : Type} [TopologicalSpace G] [ChartedSpace E G] [Group G] [LieGroup 𝓘(ℝ, E) (⊤ : ℕ∞) G]
    {a : Type} [NormedAddCommGroup a] [NormedSpace ℝ a] [CompleteSpace a]
    {A : Type} [TopologicalSpace A] [ChartedSpace a A] [AddCommGroup A]
    [LieAddGroup 𝓘(ℝ, a) (⊤ : ℕ∞) A] [DistribMulAction G A]
    [ConnectedSpace G] (qA : a →+ A) (hA : IsSmoothModuleCover (E := E) (G := G) A qA)
    (ω : LieAlg E G →L[ℝ] LieAlg E G →L[ℝ] a) (hω : IsCocycle2 A ω) :
    (IntegratesToConnected A qA ω ↔
      periodSet A ω ⊆ (qA.ker : Set a) ∧ FluxFactors A qA ω) ∧
    (ConnectedSpace A → (FluxFactors A qA ω ↔ FluxVanishes A ω)) := by sorry

end AbelianLieExt.Integrability
