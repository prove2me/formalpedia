-- Prove2me | Theorems.Thm_AlgebraicGeometry_PolarisedAbelianScheme_exists_faithfullyFlat_isThetaAdapted_isPullback_of_thetaTypeLocally
-- name    : AlgebraicGeometry.PolarisedAbelianScheme.exists_faithfullyFlat_isThetaAdapted_isPullback_of_thetaTypeLocally
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.469968+00:00
-- url     : https://prove2.me/theorems/4734270a-351e-5b0a-b69d-ec1097ae4298
-- title:
--   Theta-adapted frame for a prescribed indexing after faithfully flat base change
-- statement:
--   Fix natural numbers $g$, $N$, $n$ and a tuple $\delta : \mathrm{Fin}\,g \to \mathbb{N}$ of nonzero entries with $\prod_i \delta_i = N+1$, together with a bijection $e$ between $\mathrm{Fin}(N+1)$ and $H(\delta) = \prod_i \mathbb{Z}/\delta_i$. Let $B$ be a commutative ring carrying an element $\zeta$ with $\zeta^{N+1} = 1$ and $1 - \zeta^{j}$ a unit for all $0 < j < N+1$, let $S$ be a commutative ring and $s : \operatorname{Spec} S \to \operatorname{Spec} B$ a morphism of schemes, and let $u$ be a polarised abelian scheme over $S$ of relative dimension $g$, fibre degree $N+1$ and torsion level $n$ in the project's sense (a relative group law with commutative multiplication, fibres of topological Krull dimension $g$, a family $P_1,\dots,P_{2g}$ of $n$-torsion sections that is independent and spans the $n$-torsion of every geometric fibre, and an invertible module `pol` which is very ample by sections and has geometric fibre $H^0$-rank $N+1$). Assume `ThetaTypeLocally δ S u`: for every $S$-algebra $R$ and every $\zeta_R \in R$ with $\zeta_R^{N+1} = 1$ and $1 - \zeta_R^{j}$ a unit for $0 < j < N+1$, there are a faithfully flat étale $R$-algebra $R'$, a framed polarised abelian scheme over $R'$ and some bijection $\mathrm{Fin}(N+1) \simeq H(\delta)$ for which that framed object is theta-adapted and its underlying polarised abelian scheme is the pullback of $u$ along $S \to R \to R'$. The conclusion asserts the existence of a commutative ring $S'$ with an $S$-algebra structure making $S'$ faithfully flat over $S$, and of a framed polarised abelian scheme $X'$ over $S'$ (a polarised abelian scheme of fibre degree $N+1$ together with a projective presentation `frame` of its polarisation module into $\mathbb{P}^N_{S'}$ whose morphism is a closed immersion and whose $N+1$ sections form a section basis) such that $X'$ is theta-adapted for $\delta$ and the prescribed $e$ — i.e. there is a Schrödinger frame for the group law, polarisation and $\delta$ whose section indexed by $e(i)$ is the pullback of the $i$-th frame section for each $i$ — and such that the underlying polarised abelian scheme of $X'$ is a pullback of $u$ along $S \to S'$, in the sense that a morphism of the total spaces makes a pullback square over $\operatorname{Spec} S' \to \operatorname{Spec} S$, is compatible with the group laws and the torsion sections, and identifies the pullback of `pol`. Étaleness of $S'$ over $S$ is not asserted in the conclusion.
--
--   This is the step passing from the statement that a polarised abelian scheme is of theta type $\delta$ locally, where the indexing bijection $\mathrm{Fin}(N+1) \simeq H(\delta)$ is produced by the local datum, to a single faithfully flat base change carrying a frame adapted to a bijection fixed in advance; the root of unity $\zeta$ over $B$ supplies the separation condition needed to apply the local hypothesis. It is used in the construction of fine moduli for objects of theta type, via [`AlgebraicGeometry.PolarisedAbelianScheme.Satisfying.exists_isFineModuli_thetaTypeLocally_of_isFineModuli_framed_thetaCore`](thm.html#AlgebraicGeometry.PolarisedAbelianScheme.Satisfying.exists_isFineModuli_thetaTypeLocally_of_isFineModuli_framed_thetaCore).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_PolarisedAbelianScheme_exists_faithfullyFlat_isThetaAdapted_isPullback_of_thetaTypeLocally.lean

import Definitions.Def_AlgebraicGeometry_ThetaAdaptedFrame

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation
open scoped BigOperators TensorProduct

theorem AlgebraicGeometry.PolarisedAbelianScheme.exists_faithfullyFlat_isThetaAdapted_isPullback_of_thetaTypeLocally
    {g N n : ℕ} (δ : Fin g → ℕ) [hδ : ∀ i, NeZero (δ i)] (hδd : ∏ i, δ i = N + 1)
    (e : Fin (N + 1) ≃ ((i : Fin g) → ZMod (δ i)))
    (B : Type) [CommRing B] (ζ : B) (hζ : ζ ^ (N + 1) = 1) (hζu : ∀ j : ℕ, 0 < j → j < N + 1 → IsUnit (1 - ζ ^ j))
    (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B))
    (u : PolarisedAbelianScheme g (N + 1) n S) (hu : PolarisedAbelianScheme.ThetaTypeLocally δ S u) :
    ∃ (S' : Type) (_ : CommRing S') (_ : Algebra S S'), Module.FaithfullyFlat S S' ∧
      ∃ X' : FramedPolarisedAbelianScheme g N n S', X'.IsThetaAdapted δ e ∧
        PolarisedAbelianScheme.IsPullback (algebraMap S S') u X'.toPolarisedAbelianScheme := by sorry
