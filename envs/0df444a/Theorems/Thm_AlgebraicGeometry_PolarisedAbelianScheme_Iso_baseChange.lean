-- Prove2me | Theorems.Thm_AlgebraicGeometry_PolarisedAbelianScheme_Iso_baseChange
-- name    : AlgebraicGeometry.PolarisedAbelianScheme.Iso.baseChange
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.469968+00:00
-- url     : https://prove2.me/theorems/bbf92372-b5d6-598a-b528-3260a3a7ee49
-- title:
--   Base changes of isomorphic polarised abelian schemes are isomorphic
-- statement:
--   Fix natural numbers $g$, $d$, $n$, commutative rings $S$, $S'$ and a ring homomorphism $\varphi : S \to S'$, together with two objects $u_1, u_2$ of type `PolarisedAbelianScheme g d n S` and two objects $v_1, v_2$ of type `PolarisedAbelianScheme g d n S'` (each such object consists of a scheme with a structure morphism to the spectrum of the base ring, a commutative relative group law on its functor of points, smoothness, properness and connectedness of fibres, fibres of topological Krull dimension $g$, a family of $2g$ $n$-torsion sections which on every geometric fibre freely generate the $n$-torsion, and an invertible module `pol` which is a closed immersion by sections and has geometric fibre $H^0$-rank $d$). Assume: (i) `Iso u₁ u₂`, i.e. there is an isomorphism $e$ of the underlying schemes commuting with the structure morphisms, compatible with the group laws on $T$-points, carrying the $i$-th marked section of $u_1$ to that of $u_2$, and such that every point of $\operatorname{Spec} S$ has an open neighbourhood $U$ over which the pullback of $u_2.\mathrm{pol}$ along $e$ becomes isomorphic to $u_1.\mathrm{pol}$; (ii) for $i = 1,2$, `IsPullback φ uᵢ vᵢ`, i.e. there is $g_i : v_i.A \to u_i.A$ forming a pullback square with the structure morphisms over $\operatorname{Spec}\varphi$, compatible with the group laws, carrying marked sections to the base change of the marked sections, and with $g_i^{*}(u_i.\mathrm{pol}) \cong v_i.\mathrm{pol}$. The conclusion is `Iso v₁ v₂`.
--
--   This is the statement that the base change of a polarised abelian scheme along a ring homomorphism is determined up to isomorphism by the isomorphism class of the original object, the polarisation being compared only locally on the base. It is used in the descent arguments for polarised abelian schemes, for instance in gluing local isomorphisms over localisations away from an element and in producing a descent datum together with an isomorphism over a faithfully flat base change.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_PolarisedAbelianScheme_Iso_baseChange.lean

import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open scoped TensorProduct

theorem AlgebraicGeometry.PolarisedAbelianScheme.Iso.baseChange
    {g d n : ℕ} {S S' : Type} [CommRing S] [CommRing S'] (φ : S →+* S')
    (u₁ u₂ : PolarisedAbelianScheme g d n S) (v₁ v₂ : PolarisedAbelianScheme g d n S')
    (h : PolarisedAbelianScheme.Iso u₁ u₂)
    (h₁ : PolarisedAbelianScheme.IsPullback φ u₁ v₁) (h₂ : PolarisedAbelianScheme.IsPullback φ u₂ v₂) :
    PolarisedAbelianScheme.Iso v₁ v₂ := by sorry
