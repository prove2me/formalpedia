-- Prove2me | Theorems.Thm_AbelianLieExt_Integrability_lemma_III_7
-- name    : AbelianLieExt.Integrability.lemma_III_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T09:28:26.787241+00:00
-- url     : https://prove2.me/theorems/36eedd79-fea8-4602-af92-d76abfc59be6
-- title:
--   Lemma III.7 (corrected: γ an isomorphism), p. 14 — A ≅ B over A₀ iff θ̄_B ∘ γ = θ̄_A for an isomorphism γ: π₀(A) → π₀(B)
-- statement:
--   Let $G$ be a connected real Banach–Lie group with Lie algebra $\mathfrak g$, and let $A$ and $B$ be smooth $G$-modules with identity components $A_0 = B_0 \cong \mathfrak a/\Gamma_A$ as $G$-modules: there are coverings $q_A\colon \mathfrak a \to A_0$ and $q_B\colon \mathfrak a \to B_0$ with the same kernel $\Gamma_A$ inducing the same action $\rho_{\mathfrak a}$ of $G$ on $\mathfrak a$. Then the following are equivalent:
--
--   1. there is an isomorphism $\psi\colon A \to B$ of smooth $G$-modules (an additive diffeomorphism commuting with the actions) with $\psi|_{A_0} = \mathrm{id}_{A_0}$, i.e. $\psi \circ q_A = q_B$;
--   2. there is a group isomorphism $\gamma\colon \pi_0(A) \to \pi_0(B)$ such that the characteristic homomorphisms satisfy
--   $$\overline\theta_B \circ \gamma = \overline\theta_A\colon \pi_0(A) \to H^1_c(\mathfrak g, \mathfrak a),$$
--   that is, $\theta_B(c) - \theta_A(b) \in B^1_c(\mathfrak g, \mathfrak a)$ whenever $\gamma([b]) = [c]$.
--
--   In the Integrability Criterion this lemma identifies the group $B \subseteq \widehat G$ constructed in the proof with the given module $A$.
--
--   **Formalization Note** Real Banach scope (see the Setting definition). **Correction:** the paper's statement asks for a *homomorphism* $\gamma$, but then the "if" direction is false: for $A = A_0$ and $B = A_0 \times \mathbb Z/2$ (trivial action on $\mathbb Z/2$), $\gamma = 0$ satisfies $\overline\theta_B \circ \gamma = 0 = \overline\theta_A$, yet $A \not\cong B$. The paper's proof of the converse begins "Suppose, conversely, that $\gamma$ is an isomorphism", and the "only if" direction produces an isomorphism, so $\gamma$ is required to be an isomorphism here. $\pi_0(A)$ is encoded as $A/q_A(\mathfrak a)$.
-- source:
--   Neeb, Abelian extensions of infinite-dimensional Lie groups, arXiv:math/0402303v1, p. 14, Lemma III.7 (corrected: γ an isomorphism, as in its proof)

import Mathlib
import Definitions.Def_AbelianLieExt_Integrability_Setting

open scoped Manifold

namespace AbelianLieExt.Integrability

/-- Lemma III.7 (corrected: `γ` an isomorphism), arXiv:math/0402303v1, p. 14. -/
theorem lemma_III_7
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {G : Type} [TopologicalSpace G] [ChartedSpace E G] [Group G] [LieGroup 𝓘(ℝ, E) (⊤ : ℕ∞) G]
    {a : Type} [NormedAddCommGroup a] [NormedSpace ℝ a] [CompleteSpace a]
    {A : Type} [TopologicalSpace A] [ChartedSpace a A] [AddCommGroup A]
    [LieAddGroup 𝓘(ℝ, a) (⊤ : ℕ∞) A] [DistribMulAction G A]
    {B : Type} [TopologicalSpace B] [ChartedSpace a B] [AddCommGroup B]
    [LieAddGroup 𝓘(ℝ, a) (⊤ : ℕ∞) B] [DistribMulAction G B]
    [ConnectedSpace G] (qA : a →+ A) (hA : IsSmoothModuleCover (E := E) (G := G) A qA)
    (qB : a →+ B) (hB : IsSmoothModuleCover (E := E) (G := G) B qB)
    (hker : qA.ker = qB.ker) (hrho : ∀ g : G, rhoA (a := a) A g = rhoA B g) :
    (∃ ψ : A ≃+ B, ContMDiff 𝓘(ℝ, a) 𝓘(ℝ, a) (⊤ : ℕ∞) ψ ∧
        ContMDiff 𝓘(ℝ, a) 𝓘(ℝ, a) (⊤ : ℕ∞) ψ.symm ∧
        (∀ (g : G) (b : A), ψ (g • b) = g • ψ b) ∧ (∀ v : a, ψ (qA v) = qB v)) ↔
      (∃ γ : (A ⧸ qA.range) ≃+ (B ⧸ qB.range),
        ∀ (b : A) (c : B), γ (QuotientAddGroup.mk b) = QuotientAddGroup.mk c →
          IsCoboundary1 A (fun x : LieAlg E G => charHom (a := a) B c x - charHom (a := a) A b x)) := by sorry

end AbelianLieExt.Integrability
