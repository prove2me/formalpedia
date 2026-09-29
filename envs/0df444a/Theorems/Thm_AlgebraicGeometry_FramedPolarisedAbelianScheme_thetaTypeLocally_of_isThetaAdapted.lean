-- Prove2me | Theorems.Thm_AlgebraicGeometry_FramedPolarisedAbelianScheme_thetaTypeLocally_of_isThetaAdapted
-- name    : AlgebraicGeometry.FramedPolarisedAbelianScheme.thetaTypeLocally_of_isThetaAdapted
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.863777+00:00
-- url     : https://prove2.me/theorems/a3aae6bf-5cb9-51f8-a87c-7aa5d1f068cb
-- title:
--   Theta-adapted frames give theta type étale-locally
-- statement:
--   Fix natural numbers $g$, $N$, $n$ and a tuple $\delta : \mathrm{Fin}\,g \to \mathbb{N}$ with every $\delta_i$ nonzero and $\prod_i \delta_i = N+1$, together with a bijection $e : \mathrm{Fin}(N+1) \simeq \prod_i \mathbb{Z}/\delta_i$. Let $B$ be a commutative ring carrying an element $\zeta$ with $\zeta^{N+1} = 1$ and $1 - \zeta^{j}$ a unit for all $0 < j < N+1$, let $S$ be a commutative ring and $s : \operatorname{Spec} S \to \operatorname{Spec} B$ a morphism of schemes. Let $X$ be a framed polarised abelian scheme of invariants $(g, N, n)$ over $S$: a polarised abelian scheme $f : A \to \operatorname{Spec} S$ of fibre dimension $g$ with commutative relative group law, $2g$ independent $n$-torsion sections, invertible polarising module `pol` of geometric fibrewise $H^0$-rank $N+1$, equipped with a projective presentation `frame` of `pol` over $f$ by $N+1$ sections whose associated morphism to $\mathbb{P}^N_S$ is a closed immersion and whose sections form a section basis on the whole space. Assume $X$ is theta-adapted for $\delta$ and $e$, i.e. there is a Schrödinger frame $F$ for $f$, the group law and `pol` over $\mathrm{id}_{\operatorname{Spec} S}$ with parameters $\delta$ such that $F.\sigma(e(i))$ is the pullback of the $i$-th frame section along the first projection, for every $i$. Then the underlying polarised abelian scheme of $X$ has theta type $\delta$ locally: for every $S$-algebra $R$ and every $\zeta_R \in R$ with $\zeta_R^{N+1} = 1$ and $1 - \zeta_R^{j}$ a unit for $0 < j < N+1$, there are a commutative ring $R'$ and an $R$-algebra structure on it that is faithfully flat and étale, a framed polarised abelian scheme $X'$ over $R'$ and a bijection $\mathrm{Fin}(N+1) \simeq \prod_i \mathbb{Z}/\delta_i$ such that the underlying polarised abelian scheme of $X'$ is the pullback of that of $X$ along the composite $S \to R \to R'$, and $X'$ is theta-adapted for $\delta$ and that bijection.
--
--   This is the step passing from a single theta-adapted framed object to the local property `ThetaTypeLocally`, the shape in which theta structures in the sense of Mumford's theory of theta groups enter the moduli discussion. It is used in the construction of a fine moduli scheme for polarised abelian schemes of theta type from one for framed theta-adapted objects.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_FramedPolarisedAbelianScheme_thetaTypeLocally_of_isThetaAdapted.lean

import Definitions.Def_AlgebraicGeometry_ThetaAdaptedFrame

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation
open scoped BigOperators TensorProduct

theorem AlgebraicGeometry.FramedPolarisedAbelianScheme.thetaTypeLocally_of_isThetaAdapted
    {g N n : ℕ} (δ : Fin g → ℕ) [hδ : ∀ i, NeZero (δ i)] (hδd : ∏ i, δ i = N + 1)
    (e : Fin (N + 1) ≃ ((i : Fin g) → ZMod (δ i)))
    (B : Type) [CommRing B] (ζ : B) (hζ : ζ ^ (N + 1) = 1) (hζu : ∀ j : ℕ, 0 < j → j < N + 1 → IsUnit (1 - ζ ^ j))
    (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B))
    (X : FramedPolarisedAbelianScheme g N n S) (hX : X.IsThetaAdapted δ e) :
    PolarisedAbelianScheme.ThetaTypeLocally δ S X.toPolarisedAbelianScheme := by sorry
