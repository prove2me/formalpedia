-- Prove2me | Theorems.Thm_AbelianLieExt_Integrability_proposition_VI_3
-- name    : AbelianLieExt.Integrability.proposition_VI_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T09:28:12.941979+00:00
-- url     : https://prove2.me/theorems/d84196f1-b4a9-49ec-b3b4-2f40e02973f6
-- title:
--   Proposition VI.3 (restriction to π₁(G)), p. 23 — the flux homomorphism F_ω: π₁(G) → H¹_c(𝔤, 𝔞)
-- statement:
--   Let $G$ be a connected real Banach–Lie group with Lie algebra $\mathfrak g$, $A$ a smooth $G$-module with $A_0 \cong \mathfrak a/\Gamma_A$, and $\omega \in Z^2_c(\mathfrak g, \mathfrak a)$. Then there is a map $F\colon \pi_1(G) \to \mathrm{Lin}(\mathfrak g, \mathfrak a)$ into continuous linear maps such that
--
--   1. $F(c) \in Z^1_c(\mathfrak g, \mathfrak a)$ for every $c \in \pi_1(G)$;
--   2. $\widetilde F_\omega(\ell) - F(c) \in B^1_c(\mathfrak g, \mathfrak a)$ for every smooth loop $\ell$ at $1$ representing $c$;
--   3. $F(c_1 c_2) - F(c_1) - F(c_2) \in B^1_c(\mathfrak g, \mathfrak a)$ for all $c_1, c_2 \in \pi_1(G)$.
--
--   In other words, the **flux homomorphism**
--
--   $$F_\omega\colon \pi_1(G) \to H^1_c(\mathfrak g, \mathfrak a), \qquad [\ell] \mapsto [\widetilde F_\omega(\ell)],$$
--
--   is well defined and is a group homomorphism. Its relation to the characteristic homomorphism of $A$ is condition (2) of the Integrability Criterion.
--
--   **Formalization Note** Real Banach scope (see the Setting definition). Only the last assertion of Proposition VI.3, the restriction to $\pi_1(G)$, is formalized; the 1-cocycle $F_\omega$ on the universal covering group $\widetilde G$ with values in $\widehat H^1_c(\mathfrak g, \mathfrak a)$ is not used by Theorem VI.7. The quotient $H^1_c$ is not built; equality of classes is stated as "the difference is a coboundary". $\pi_1(G)$ is Mathlib's fundamental group at $1$, with smooth loop representatives.
-- source:
--   Neeb, Abelian extensions of infinite-dimensional Lie groups, arXiv:math/0402303v1, p. 23, Proposition VI.3 (restriction to π₁(G))

import Mathlib
import Definitions.Def_AbelianLieExt_Integrability_Setting

open scoped Manifold

namespace AbelianLieExt.Integrability

/-- Proposition VI.3 (restriction to `π₁(G)`), arXiv:math/0402303v1, p. 23: the flux homomorphism
`F_ω : π₁(G) → H¹_c(𝔤, 𝔞)` is well defined. -/
theorem proposition_VI_3
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {G : Type} [TopologicalSpace G] [ChartedSpace E G] [Group G] [LieGroup 𝓘(ℝ, E) (⊤ : ℕ∞) G]
    {a : Type} [NormedAddCommGroup a] [NormedSpace ℝ a] [CompleteSpace a]
    {A : Type} [TopologicalSpace A] [ChartedSpace a A] [AddCommGroup A]
    [LieAddGroup 𝓘(ℝ, a) (⊤ : ℕ∞) A] [DistribMulAction G A]
    [ConnectedSpace G] (qA : a →+ A) (hA : IsSmoothModuleCover (E := E) (G := G) A qA)
    (ω : LieAlg E G →L[ℝ] LieAlg E G →L[ℝ] a) (hω : IsCocycle2 A ω) :
    ∃ F : FundamentalGroup G 1 → (LieAlg E G →L[ℝ] a),
      (∀ c, IsCocycle1 A (F c)) ∧
      (∀ (c : FundamentalGroup G 1) (ℓ : ℝ → G), IsSmoothLoopRep (E := E) c ℓ →
        IsCoboundary1 A (fun x => fluxCocycle A ω ℓ x - F c x)) ∧
      (∀ c₁ c₂ : FundamentalGroup G 1,
        IsCoboundary1 A (fun x => F (c₁ * c₂) x - F c₁ x - F c₂ x)) := by sorry

end AbelianLieExt.Integrability
