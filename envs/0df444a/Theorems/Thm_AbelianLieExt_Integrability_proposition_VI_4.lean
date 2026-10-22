-- Prove2me | Theorems.Thm_AbelianLieExt_Integrability_proposition_VI_4
-- name    : AbelianLieExt.Integrability.proposition_VI_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T09:28:19.113081+00:00
-- url     : https://prove2.me/theorems/9d1c198a-093f-4cd7-8777-953b6a9ee9cf
-- title:
--   Proposition VI.4 (2), (3), p. 24 — F_ω = −θ̄_A ∘ δ on π₁(G), and F_ω(π₁(G)) = {0} if A is connected
-- statement:
--   Let $G$ be a connected real Banach–Lie group with Lie algebra $\mathfrak g$, $A$ a smooth $G$-module with $A_0 \cong \mathfrak a/\Gamma_A$, $\omega \in Z^2_c(\mathfrak g, \mathfrak a)$, and let $A \hookrightarrow \widehat G \overset{q}{\twoheadrightarrow} G$ be a Lie group extension of $G$ by $A$ whose Lie algebra is $\widehat{\mathfrak g} \cong \mathfrak a \oplus_\omega \mathfrak g$. Let $\delta\colon \pi_1(G) \to \pi_0(A)$ be the connecting homomorphism of the principal $A$-bundle $q$: for a loop $\ell$ at $1$ and a lift $\hat\ell$ of $\ell$ to $\widehat G$ with $\hat\ell(0) = 1$, $\hat\ell(1) \in A$ and $\delta([\ell]) = [\hat\ell(1)]$. Then:
--
--   1. (item (2)) for every smooth loop $\ell$ at $1$ and every continuous lift $\hat\ell$ on $[0,1]$ with $\hat\ell(0) = 1$, the endpoint $\hat\ell(1)$ lies in $A$, and for $b = \hat\ell(1)$
--   $$\widetilde F_\omega(\ell) + \theta_A(b) \in B^1_c(\mathfrak g, \mathfrak a), \qquad\text{i.e.}\qquad F_\omega = -\overline\theta_A \circ \delta\colon \pi_1(G) \to H^1_c(\mathfrak g, \mathfrak a);$$
--   2. (item (3)) if $A$ is connected, then $\widetilde F_\omega(\ell) \in B^1_c(\mathfrak g, \mathfrak a)$ for every smooth loop $\ell$ at $1$, i.e. $F_\omega(\pi_1(G)) = \{0\}$.
--
--   This gives the necessity of condition (2) in the Integrability Criterion: if $\widehat G$ exists, the flux homomorphism factors through the characteristic homomorphism of $A$.
--
--   **Formalization Note** Real Banach scope (see the Setting definition). Item (1) of the proposition, involving the adjoint action (6.4) of $\widehat G$ on $\widehat{\mathfrak g}$ and the cocycle $\overline\theta$ on $\widehat G/A_0$, is not formalized. $\delta$ is not defined as a map; its defining property via path lifting is written out. The extension is an `Extension` structure (see the Setting definition), which includes the conjugation action prescribed by Definition II.4.
-- source:
--   Neeb, Abelian extensions of infinite-dimensional Lie groups, arXiv:math/0402303v1, p. 24, Proposition VI.4 (2), (3)

import Mathlib
import Definitions.Def_AbelianLieExt_Integrability_Setting

open scoped Manifold

namespace AbelianLieExt.Integrability

/-- Proposition VI.4 (2), (3), arXiv:math/0402303v1, p. 24: `F_ω = −θ̄_A ∘ δ` on `π₁(G)`, and
`F_ω(π₁(G)) = 0` when `A` is connected. -/
theorem proposition_VI_4
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {G : Type} [TopologicalSpace G] [ChartedSpace E G] [Group G] [LieGroup 𝓘(ℝ, E) (⊤ : ℕ∞) G]
    {a : Type} [NormedAddCommGroup a] [NormedSpace ℝ a] [CompleteSpace a]
    {A : Type} [TopologicalSpace A] [ChartedSpace a A] [AddCommGroup A]
    [LieAddGroup 𝓘(ℝ, a) (⊤ : ℕ∞) A] [DistribMulAction G A]
    [ConnectedSpace G] (qA : a →+ A) (hA : IsSmoothModuleCover (E := E) (G := G) A qA)
    (ω : LieAlg E G →L[ℝ] LieAlg E G →L[ℝ] a) (hω : IsCocycle2 A ω)
    (X : Extension A qA ω) :
    -- (2): for a smooth loop `ℓ` at `1` and a lift `ℓ̂` to `Ĝ` from `1`, `δ([ℓ]) = [ℓ̂(1)]` and
    -- `F̃_ω(ℓ) + θ_A(ℓ̂(1)) ∈ B¹_c(𝔤, 𝔞)`
    (∀ (ℓ : ℝ → G) (ℓhat : ℝ → X.H), ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (⊤ : ℕ∞) ℓ →
      ℓ 0 = 1 → ℓ 1 = 1 →
      ContinuousOn ℓhat (Set.Icc 0 1) → (∀ t ∈ Set.Icc (0 : ℝ) 1, X.q (ℓhat t) = ℓ t) →
      ℓhat 0 = 1 →
      (∃ b : A, X.ι b = ℓhat 1) ∧
      ∀ b : A, X.ι b = ℓhat 1 →
        IsCoboundary1 A (fun x => fluxCocycle A ω ℓ x + charHom A b x)) ∧
    -- (3)
    (ConnectedSpace A → ∀ ℓ : ℝ → G, ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (⊤ : ℕ∞) ℓ →
      ℓ 0 = 1 → ℓ 1 = 1 → IsCoboundary1 A (fluxCocycle A ω ℓ)) := by sorry

end AbelianLieExt.Integrability
