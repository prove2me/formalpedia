-- Prove2me | Theorems.Thm_AlgebraicGeometry_PolarisedAbelianScheme_isOfType_of_isPullback
-- name    : AlgebraicGeometry.PolarisedAbelianScheme.isOfType_of_isPullback
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.469968+00:00
-- url     : https://prove2.me/theorems/434cb6ad-dfc3-5c22-a274-2dde173b2c9b
-- title:
--   Being of type δ is stable under base change
-- statement:
--   Fix natural numbers $g,d,n$ and a vector $\delta : \mathrm{Fin}\,g \to \mathbb{N}$, commutative rings $S$ and $S'$ (in the bottom universe) and a ring homomorphism $\varphi : S \to S'$, together with polarised abelian schemes $u$ over $S$ and $u'$ over $S'$ with the same numerical data $(g,d,n)$, i.e. structures consisting of a scheme with a morphism to $\operatorname{Spec} S$ (resp. $\operatorname{Spec} S'$), a commutative relative group law, the property bundle `AbelianSchemePropertyBundle`, fibres of topological Krull dimension $g$, a family $P : \mathrm{Fin}(2g) \to$ sections killed by $n$ that is independent and spanning on geometric fibres, and an invertible module `pol` which embeds the scheme by its sections as a closed subscheme of projective space and whose geometric-fibre $H^0$ has rank $d$ over every algebraically closed field. Assume $u'$ is a base change of $u$ along $\varphi$ in the sense of `PolarisedAbelianScheme.IsPullback`: there is a morphism $g_A : u'.A \to u.A$ making the square formed by $g_A$, $u'.f$, $u.f$ and $\operatorname{Spec}\varphi$ cartesian, such that $g_A$ is multiplicative on $T$-points (the product of $x,y$ over $t'$ composed with $g_A$ equals the product over $t' \circ \operatorname{Spec}\varphi$ of the composites $x \circ g_A$, $y \circ g_A$), such that $(u'.P\,i)$ followed by $g_A$ equals $\operatorname{Spec}\varphi$ followed by $u.P\,i$ for all $i$, and such that the pullback of $u.\mathrm{pol}$ along $g_A$ is isomorphic to $u'.\mathrm{pol}$. Assume further that $u$ is of type $\delta$, i.e. there is a faithfully flat étale $S$-algebra $T$ and a family $x$ of $\operatorname{Spec} T$-points of $u.A$ over $u.f$ indexed by the group $\mathrm{typeGroup}\,\delta = \bigl(\prod_i \mathbb{Z}/\delta_i\bigr)^2$ such that: $x$ is a homomorphism ($x_0$ is the unit section and $x_{h+h'}$ is the product of $x_h$ and $x_{h'}$); the $x_h$ remain pairwise distinct after composing with any map to the spectrum of an algebraically closed field; and for every $T$-algebra $R$ and every $R$-point $y$ of $u.A$ over $u.f$, $y$ lies in the kernel of the polarisation in the sense of `Polarisation.MemKernel` (the pullback along the slice at $y$ of the Mumford bundle of $u.\mathrm{pol}$ is `LocIsoOnBase`-related over the base to the unit module) if and only if there are finitely many elements $r_1,\dots,r_m$ of $R$ generating the unit ideal such that over each localisation $R[1/r_j]$ the point $y$ coincides with the base change of some $x_h$. The conclusion is that $u'$ is of type $\delta$ in the same sense.
--
--   This records that the condition of having polarisation kernel étale-locally isomorphic to the constant group attached to the elementary divisors $\delta$ — the classical notion of a polarisation of type $\delta$ — descends through the base-change relation between polarised abelian schemes. It is used in the verification that the rooted symmetric-of-type condition is preserved under base change, which is what makes the corresponding moduli predicate functorial in the base ring.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_PolarisedAbelianScheme_isOfType_of_isPullback.lean

import Definitions.Def_AlgebraicGeometry_ThetaAdaptedFrame
import Definitions.Def_AlgebraicGeometry_ProjSpace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
attribute [local instance] MvPolynomial.gradedAlgebra
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation
open scoped BigOperators TensorProduct

theorem AlgebraicGeometry.PolarisedAbelianScheme.isOfType_of_isPullback
    {g d n : ℕ} (δ : Fin g → ℕ) {S S' : Type} [CommRing S] [CommRing S'] (φ : S →+* S')
    (u : PolarisedAbelianScheme g d n S) (u' : PolarisedAbelianScheme g d n S')
    (h : PolarisedAbelianScheme.IsPullback φ u u') (hu : PolarisedAbelianScheme.IsOfType δ u) :
    PolarisedAbelianScheme.IsOfType δ u' := by sorry
