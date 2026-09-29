-- Prove2me | Theorems.Thm_AlgebraicGeometry_PolarisedAbelianScheme_thetaTypeLocally_of_iso
-- name    : AlgebraicGeometry.PolarisedAbelianScheme.thetaTypeLocally_of_iso
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.469968+00:00
-- url     : https://prove2.me/theorems/c07e9672-ee8d-55eb-a70f-eae67a726a3c
-- title:
--   Étale-local theta type is invariant under isomorphism
-- statement:
--   Fix natural numbers $g, N, n$ and a tuple $\delta : \mathrm{Fin}\,g \to \mathbb{N}$ with every $\delta(i)$ nonzero, and let $S$ be a commutative ring. Let $u, u'$ be polarised abelian schemes over $S$ of type $(g, N+1, n)$, that is, schemes $A \to \operatorname{Spec} S$ carrying a commutative relative group law, the property bundle of an abelian scheme, all fibres of dimension $g$, a family of $2g$ sections killed by $n$ that are independent and generate the $n$-torsion of every geometric fibre, and an invertible module, very ample through sections, whose geometric fibre $H^0$ has rank $N+1$. Assume `PolarisedAbelianScheme.Iso u u'`: there is an isomorphism $e : u.A \cong u'.A$ over $\operatorname{Spec} S$ compatible with the two group laws on $T$-points for all $T \to \operatorname{Spec} S$, carrying each level section $P_i$ of $u$ to that of $u'$, and such that every point of $\operatorname{Spec} S$ has an open neighbourhood $U$ over which $e^{*}(u'.pol)$ and $u.pol$ become isomorphic after restriction to the preimage of $U$. Then the predicate `PolarisedAbelianScheme.ThetaTypeLocally δ S`, which holds for $u$ by hypothesis, also holds for $u'$; it asks that for every $S$-algebra $R$ and every $\zeta \in R$ with $\zeta^{N+1} = 1$ and $1 - \zeta^{j}$ a unit for $0 < j < N+1$, there are a faithfully flat étale $R$-algebra $R'$, a framed polarised abelian scheme $X'$ over $R'$ and a bijection $\mathrm{Fin}(N+1) \simeq \prod_i \mathbb{Z}/\delta(i)$, such that $X'$ is the base change of the given object along $S \to R \to R'$ and $X'$ is theta-adapted for $\delta$ and that bijection.
--
--   This records that being of theta type $\delta$ étale-locally over the base depends only on the isomorphism class of a polarised abelian scheme with level structure, the isomorphism being required to match the polarisations only locally on $\operatorname{Spec} S$. It is used in the construction of fine moduli for quaternionic structures in the Čerednik–Drinfeld part of the development.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_PolarisedAbelianScheme_thetaTypeLocally_of_iso.lean

import Definitions.Def_AlgebraicGeometry_ThetaAdaptedFrame
import Definitions.Def_AlgebraicGeometry_ProjSpace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

attribute [local instance] MvPolynomial.gradedAlgebra

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation
open scoped BigOperators TensorProduct

theorem AlgebraicGeometry.PolarisedAbelianScheme.thetaTypeLocally_of_iso
    {g N n : ℕ} (δ : Fin g → ℕ) [hδ : ∀ i, NeZero (δ i)]
    {S : Type} [CommRing S] (u u' : PolarisedAbelianScheme g (N + 1) n S)
    (h : PolarisedAbelianScheme.Iso u u') (hu : PolarisedAbelianScheme.ThetaTypeLocally δ S u) :
    PolarisedAbelianScheme.ThetaTypeLocally δ S u' := by sorry
