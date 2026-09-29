-- Prove2me | Theorems.Thm_AlgebraicGeometry_PolarisedAbelianScheme_rootedSymmetricOfType_of_isPullback
-- name    : AlgebraicGeometry.PolarisedAbelianScheme.rootedSymmetricOfType_of_isPullback
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.469968+00:00
-- url     : https://prove2.me/theorems/0db7acfa-324f-571c-9b37-14e5e88ea06c
-- title:
--   Base change preserves symmetric polarisations of type δ with principal root
-- statement:
--   Fix natural numbers $g$, $d$, $n$ and a tuple $\delta : \mathrm{Fin}\,g \to \mathbb{N}$, commutative rings $S$, $S'$ and a ring homomorphism $\varphi : S \to S'$, together with objects $u$ of `PolarisedAbelianScheme g d n S` and $u'$ of `PolarisedAbelianScheme g d n S'` (each consisting of a scheme over the base, a commutative relative group law, the property bundle of an abelian scheme, fibres of topological Krull dimension $g$, a family $P_0,\dots,P_{2g-1}$ of $n$-torsion sections freely generating the $n$-torsion of every geometric fibre, and an invertible module `pol` whose sections give a closed immersion and whose geometric fibrewise $H^0$ has dimension $d$). Assume `PolarisedAbelianScheme.IsPullback φ u u'`, i.e. there is a morphism $g_A : u'.A \to u.A$ making the square with the two structure morphisms and $\mathrm{Spec}\,\varphi$ cartesian, compatible with the two group laws on relative points, carrying each $P_i$ of $u'$ to the corresponding $P_i$ of $u$, and such that the pullback of `u.pol` along $g_A$ is isomorphic to `u'.pol`. Assume further that $u$ satisfies `RootedSymmetricOfType δ`, that is: `u.pol` is symmetric (the pullback along the inversion morphism is locally isomorphic to `u.pol` over the base), $u$ is of type $\delta$, and $u$ has a principal root. Then $u'$ satisfies the same three conditions over $S'$.
--
--   This records that the notion of a polarised abelian scheme which is symmetric, of type $\delta$ and possessing a principal root is stable under base change of the base ring, as needed for the functorial treatment of such data. It is used in the derivation of the local theta-type description `thetaTypeLocally_of_rootedSymmetricOfType`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_PolarisedAbelianScheme_rootedSymmetricOfType_of_isPullback.lean

import Definitions.Def_AlgebraicGeometry_ThetaAdaptedFrame
import Definitions.Def_AlgebraicGeometry_ProjSpace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

attribute [local instance] MvPolynomial.gradedAlgebra

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation
open scoped BigOperators TensorProduct

theorem AlgebraicGeometry.PolarisedAbelianScheme.rootedSymmetricOfType_of_isPullback
    {g d n : ℕ} (δ : Fin g → ℕ)
    {S S' : Type} [CommRing S] [CommRing S'] (φ : S →+* S')
    (u : PolarisedAbelianScheme g d n S) (u' : PolarisedAbelianScheme g d n S')
    (h : PolarisedAbelianScheme.IsPullback φ u u') (hu : PolarisedAbelianScheme.RootedSymmetricOfType δ S u) :
    PolarisedAbelianScheme.RootedSymmetricOfType δ S' u' := by sorry
