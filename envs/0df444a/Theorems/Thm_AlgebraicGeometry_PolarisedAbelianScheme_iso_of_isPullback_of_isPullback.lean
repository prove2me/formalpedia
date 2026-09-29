-- Prove2me | Theorems.Thm_AlgebraicGeometry_PolarisedAbelianScheme_iso_of_isPullback_of_isPullback
-- name    : AlgebraicGeometry.PolarisedAbelianScheme.iso_of_isPullback_of_isPullback
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.469968+00:00
-- url     : https://prove2.me/theorems/eff5d644-00df-5192-a61b-eea3961b2771
-- title:
--   Uniqueness of the base change of a polarised abelian scheme
-- statement:
--   Fix natural numbers $g, d, n$, commutative rings $S$ and $S'$, and a ring homomorphism $\varphi : S \to S'$. Let $u$ be a polarised abelian scheme of type $(g,d,n)$ over $S$ — that is, a scheme $u.A$ with a structure morphism to $\operatorname{Spec} S$ carrying a commutative relative group law on its functor of points, smooth, proper, with connected fibres of topological Krull dimension $g$, together with $2g$ sections killed by $n$ that are independent and span the $n$-torsion on every geometrically closed fibre, and an invertible module $u.\mathrm{pol}$ defining a closed immersion by sections with geometric fibrewise $H^0$-rank $d$ — and let $v, v'$ be two such objects over $S'$. Assume both $v$ and $v'$ are pullbacks of $u$ along $\varphi$ in the sense of `PolarisedAbelianScheme.IsPullback`: for each of them there is a morphism to $u.A$ making the square with the two structure morphisms and $\operatorname{Spec}\varphi$ cartesian, compatible with the relative group laws on $T$-points, sending the $i$-th marked section to the composite of $\operatorname{Spec}\varphi$ with the $i$-th marked section of $u$, and admitting an isomorphism from the pullback of $u.\mathrm{pol}$ to its own polarisation. The conclusion is `PolarisedAbelianScheme.Iso v v'`: there is an isomorphism $e : v.A \cong v'.A$ over $\operatorname{Spec} S'$ which is a homomorphism for the relative group laws on $T$-points, carries each marked section of $v$ to that of $v'$, and is such that every point of $\operatorname{Spec} S'$ has a neighbourhood $U$ over which the pullback of $v'.\mathrm{pol}$ along $e$ becomes isomorphic to $v.\mathrm{pol}$.
--
--   This is the uniqueness of a fibre product, applied to the base change of a polarised abelian scheme along a fixed ring homomorphism: two realisations of the pullback are isomorphic as polarised abelian schemes with level structure. It is used by the lemmas on `PolarisedAbelianScheme.Satisfying` that compare marked points and isomorphism classes under base change along composable and finite free maps.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_PolarisedAbelianScheme_iso_of_isPullback_of_isPullback.lean

import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open scoped TensorProduct

theorem AlgebraicGeometry.PolarisedAbelianScheme.iso_of_isPullback_of_isPullback
    {g d n : ℕ} {S S' : Type} [CommRing S] [CommRing S'] (φ : S →+* S')
    (u : PolarisedAbelianScheme g d n S) (v v' : PolarisedAbelianScheme g d n S')
    (h : PolarisedAbelianScheme.IsPullback φ u v) (h' : PolarisedAbelianScheme.IsPullback φ u v') :
    PolarisedAbelianScheme.Iso v v' := by sorry
