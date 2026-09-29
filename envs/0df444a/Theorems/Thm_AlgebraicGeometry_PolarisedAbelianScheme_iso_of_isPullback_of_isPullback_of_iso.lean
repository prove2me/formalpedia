-- Prove2me | Theorems.Thm_AlgebraicGeometry_PolarisedAbelianScheme_iso_of_isPullback_of_isPullback_of_iso
-- name    : AlgebraicGeometry.PolarisedAbelianScheme.iso_of_isPullback_of_isPullback_of_iso
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.469968+00:00
-- url     : https://prove2.me/theorems/cd2ed96a-9362-51c6-967a-1a9e7603e428
-- title:
--   Isomorphism of polarised abelian schemes descends along base change
-- statement:
--   Fix natural numbers $g,d,n$, commutative rings $S,S'$ and a ring homomorphism $\varphi \colon S \to S'$. Let $u_1,u_2$ be objects of `PolarisedAbelianScheme g d n S` and $u_1',u_2'$ objects of `PolarisedAbelianScheme g d n S'`; such an object consists of a scheme $A$ with a morphism $f \colon A \to \operatorname{Spec} S$, a commutative relative group law $L$ on the functor of points of $f$, the property bundle asserting $f$ smooth, proper with connected fibres and admitting a group law, all fibres of topological Krull dimension $g$, sections $P_i$ ($i < 2g$) killed by $n$ that on every geometric fibre over an algebraically closed field freely generate and exhaust the $n$-torsion, and an invertible module `pol` on $A$ which is very ample for $f$ in the sense of defining a closed immersion into projective space by sections and has geometric fibrewise $H^0$-rank $d$. Assume `PolarisedAbelianScheme.IsPullback φ u₁ u₁'` and `PolarisedAbelianScheme.IsPullback φ u₂ u₂'`, i.e. for $i=1,2$ there is $g_i \colon u_i'.A \to u_i.A$ making $(g_i, u_i'.f, u_i.f, \operatorname{Spec}\varphi)$ a cartesian square, compatible with the group laws on $T$-points, satisfying $(u_i'.P_j) \circ$-composed-with $g_i$ equal to $\operatorname{Spec}\varphi$ followed by $u_i.P_j$ for all $j$, and with $g_i^{*}(u_i.\mathrm{pol}) \cong u_i'.\mathrm{pol}$. Assume further `PolarisedAbelianScheme.Iso u₁ u₂`: an isomorphism $e \colon u_1.A \cong u_2.A$ over $\operatorname{Spec} S$, multiplicative on $T$-points, carrying each $u_1.P_i$ to $u_2.P_i$, and such that every point of $\operatorname{Spec} S$ has a neighbourhood $U$ over which the pullbacks to $u_1.f^{-1}U$ of $e^{*}(u_2.\mathrm{pol})$ and of $u_1.\mathrm{pol}$ are isomorphic. The conclusion is `PolarisedAbelianScheme.Iso u₁' u₂'`, the same relation over $S'$.
--
--   This is the statement that the isomorphism relation on linearly polarised abelian schemes with full level-$n$ structure is compatible with base change: a cartesian base change along $\operatorname{Spec}\varphi$ of isomorphic objects over $S$ yields isomorphic objects over $S'$. It is used in the treatment of the moduli problem for such objects, notably in the fine-moduli statements for `PolarisedAbelianScheme.Satisfying` and in the transitivity argument for points of finite free type.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_PolarisedAbelianScheme_iso_of_isPullback_of_isPullback_of_iso.lean

import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.PolarisedAbelianScheme

universe u

theorem AlgebraicGeometry.PolarisedAbelianScheme.iso_of_isPullback_of_isPullback_of_iso {g d n : ℕ}
    {S S' : Type u} [CommRing S] [CommRing S'] (φ : S →+* S')
    {u₁ u₂ : PolarisedAbelianScheme g d n S} {u₁' u₂' : PolarisedAbelianScheme g d n S'}
    (h₁ : PolarisedAbelianScheme.IsPullback φ u₁ u₁') (h₂ : PolarisedAbelianScheme.IsPullback φ u₂ u₂')
    (h : PolarisedAbelianScheme.Iso u₁ u₂) : PolarisedAbelianScheme.Iso u₁' u₂' := by sorry
