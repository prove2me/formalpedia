-- Prove2me | Theorems.Thm_AlgebraicGeometry_FramedPolarisedAbelianScheme_isThetaAdapted_of_iso
-- name    : AlgebraicGeometry.FramedPolarisedAbelianScheme.isThetaAdapted_of_iso
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.863777+00:00
-- url     : https://prove2.me/theorems/a2aabbe7-11f1-56dd-b716-178109acea67
-- title:
--   Theta-adaptedness is invariant under isomorphism of framed polarised abelian schemes
-- statement:
--   Fix natural numbers $g$, $N$, $n$, a tuple $\delta : \mathrm{Fin}\,g \to \mathbb{N}$ with every $\delta i$ nonzero, and a bijection $e$ between $\mathrm{Fin}(N+1)$ and the product group $\prod_i \mathbb{Z}/\delta i$. Let $S$ be a commutative ring and let $X, X'$ be framed polarised abelian schemes of invariants $(g,N,n)$ over $S$: each consists of a polarised abelian scheme $A \to \operatorname{Spec} S$ of relative dimension $g$ with commutative relative group law, $2g$ independent spanning $n$-torsion sections, and an invertible module `pol` with geometric fibre $h^0$ equal to $N+1$, together with a `ProjPresentation` of `pol` over $f$ of size $N$ — a family $\sigma_0,\dots,\sigma_N$ of global sections and a morphism to $\mathbb{P}^N_S$ compatible with the structure morphism and with the ratios of the $\sigma_i$ — whose morphism to $\mathbb{P}^N_S$ is a closed immersion and whose sections form a section basis on $\top$. Assume `FramedPolarisedAbelianScheme.Iso X X'`, i.e. there is an isomorphism $\varepsilon : X.A \cong X'.A$ over $S$ with $\varepsilon$ followed by $X'.\mathrm{frame.toProj}$ equal to $X.\mathrm{frame.toProj}$, compatible with the relative group laws on points over any base, carrying each $P_i$ to $P'_i$, and such that every point of $\operatorname{Spec} S$ has a neighbourhood $U$ over which the pullback of $X'.\mathrm{pol}$ along $\varepsilon$ is isomorphic to $X.\mathrm{pol}$. Assume further that $X$ is theta-adapted for $(\delta, e)$: there is a Schrödinger frame $F$ for $(X.f, X.L, X.\mathrm{pol})$ over the identity of $\operatorname{Spec} S$ with multiplicities $\delta$ — a family of sections indexed by $\prod_i \mathbb{Z}/\delta i$ forming a basis in the sense that $c \mapsto \sum_h \mathrm{baseScalar}(c\,h)\cdot \sigma_h$ is bijective, together with lifts of $\prod_i \mathbb{Z}/\delta i$ and of its character group to theta points acting on these sections by translation and by scaling — whose section at $e(i)$ is the pullback of $X.\mathrm{frame}.\sigma_i$ along the first projection of the pullback of $X.f$ with the identity, for every $i \in \mathrm{Fin}(N+1)$. The conclusion is that $X'$ is theta-adapted for the same $(\delta, e)$.
--
--   This is the statement that theta-adaptedness of a frame is a property of the isomorphism class of a framed polarised abelian scheme, so that it descends to a condition on points of the moduli problem rather than on chosen frames. It is used in the construction of the theta-type locus and in the passage from a fine moduli space for framed theta-core data to one for the theta type.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_FramedPolarisedAbelianScheme_isThetaAdapted_of_iso.lean

import Definitions.Def_AlgebraicGeometry_ThetaAdaptedFrame
import Definitions.Def_AlgebraicGeometry_ProjSpace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

attribute [local instance] MvPolynomial.gradedAlgebra

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation
open scoped BigOperators TensorProduct

theorem AlgebraicGeometry.FramedPolarisedAbelianScheme.isThetaAdapted_of_iso
    {g N n : ℕ} (δ : Fin g → ℕ) [hδ : ∀ i, NeZero (δ i)] (e : Fin (N + 1) ≃ ((i : Fin g) → ZMod (δ i)))
    {S : Type} [CommRing S]
    (X X' : FramedPolarisedAbelianScheme g N n S)
    (h : FramedPolarisedAbelianScheme.Iso X X') (hX : X.IsThetaAdapted δ e) :
    X'.IsThetaAdapted δ e := by sorry
