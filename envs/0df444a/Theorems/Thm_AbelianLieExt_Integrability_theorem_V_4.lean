-- Prove2me | Theorems.Thm_AbelianLieExt_Integrability_theorem_V_4
-- name    : AbelianLieExt.Integrability.theorem_V_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T09:28:11.193454+00:00
-- url     : https://prove2.me/theorems/ef0fc27d-1185-4188-b8b7-02a387dce587
-- title:
--   Theorem V.4, (1) ⇔ (4), p. 20 — for simply connected G and A = 𝔞/Γ_A, 𝔞 ⊕_ω 𝔤 integrates iff Π_ω ⊆ Γ_A
-- statement:
--   Let $G$ be a connected, simply connected real Banach–Lie group with Lie algebra $\mathfrak g$, and let $A$ be a smooth $G$-module of the form $A = \mathfrak a/\Gamma_A$, that is, $q_A\colon \mathfrak a \to A$ is a surjective smooth homomorphism and local diffeomorphism with discrete kernel $\Gamma_A$, intertwining the actions. Let $\omega \in Z^2_c(\mathfrak g, \mathfrak a)$ be a continuous 2-cocycle with period group $\Pi_\omega$. Then
--
--   $$\mathfrak a \oplus_\omega \mathfrak g \text{ integrates to a Lie group extension } A \hookrightarrow \widehat G \twoheadrightarrow G \iff \Pi_\omega \subseteq \Gamma_A.$$
--
--   This is the simply connected case of the integrability problem; the general Integrability Criterion (Theorem VI.7) is obtained by applying it to the universal covering group of $G$ and then dividing out a lift of $\pi_1(G)$.
--
--   **Formalization Note** Real Banach scope (see the Setting definition). Only the equivalence (1) ⇔ (4) of Theorem V.4 is formalized; items (2), (3) and (5) involve locally smooth group cohomology $H^2_s(G,A)$ and the derivation map $D$, which are not defined here. "Integrates" is the existence of an actual Lie group extension with the prescribed conjugation action and with Lie algebra equivalent to $\mathfrak a \oplus_\omega \mathfrak g$ (`IntegratesTo`); $\widehat G$ is not required to be connected, as in item (1) of the paper.
-- source:
--   Neeb, Abelian extensions of infinite-dimensional Lie groups, arXiv:math/0402303v1, p. 20, Theorem V.4, (1) ⇔ (4)

import Mathlib
import Definitions.Def_AbelianLieExt_Integrability_Setting

open scoped Manifold

namespace AbelianLieExt.Integrability

/-- Theorem V.4, (1) ⇔ (4), arXiv:math/0402303v1, p. 20: for simply connected `G` and
`A = 𝔞/Γ_A`, `𝔞 ⊕_ω 𝔤` integrates to `A ↪ Ĝ ↠ G` iff `Π_ω ⊆ Γ_A`. -/
theorem theorem_V_4
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {G : Type} [TopologicalSpace G] [ChartedSpace E G] [Group G] [LieGroup 𝓘(ℝ, E) (⊤ : ℕ∞) G]
    {a : Type} [NormedAddCommGroup a] [NormedSpace ℝ a] [CompleteSpace a]
    {A : Type} [TopologicalSpace A] [ChartedSpace a A] [AddCommGroup A]
    [LieAddGroup 𝓘(ℝ, a) (⊤ : ℕ∞) A] [DistribMulAction G A]
    [SimplyConnectedSpace G] (qA : a →+ A) (hA : IsSmoothModuleCover (E := E) (G := G) A qA)
    (hqA : Function.Surjective qA)
    (ω : LieAlg E G →L[ℝ] LieAlg E G →L[ℝ] a) (hω : IsCocycle2 A ω) :
    IntegratesTo A qA ω ↔ periodSet A ω ⊆ (qA.ker : Set a) := by sorry

end AbelianLieExt.Integrability
