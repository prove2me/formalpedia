-- Prove2me | Theorems.Thm_AlgebraicGeometry_PolarisedAbelianScheme_exists_isPullback
-- name    : AlgebraicGeometry.PolarisedAbelianScheme.exists_isPullback
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.469968+00:00
-- url     : https://prove2.me/theorems/8817697b-39ae-5dca-8214-5eaeb2e5ede8
-- title:
--   Existence of base changes of polarised abelian schemes
-- statement:
--   Let $g, d, n$ be natural numbers, let $S$ and $S'$ be commutative rings and let $\varphi : S \to S'$ be a ring homomorphism. Let $u$ be a polarised abelian scheme of type $(g,d,n)$ over $S$, that is: a scheme $A$ with a morphism $f : A \to \operatorname{Spec} S$, a relative group law $L$ on $f$ (functorial multiplication, unit and inverse on $S$-points of $f$ over arbitrary test schemes, associative, unital, with inverses, and natural in the test scheme) which is commutative; the property bundle asserting that $f$ is smooth and proper, that every fibre $f^{-1}(s)$ is connected, and that $f$ carries some relative group law; the condition that every fibre $f^{-1}(s)$ has topological Krull dimension $g$; a family $P_0,\dots,P_{2g-1}$ of sections of $f$ over $\operatorname{Spec} S$, each killed by $n$-fold iterated addition, such that over every algebraically closed field $k$ and every ring map $S \to k$ the $n$-fold combinations $\sum c_i P_i$ with $c_i \in \mathbb{Z}/n$ are pairwise distinct and exhaust the $n$-torsion of the group of $k$-points of $f$; and a module $\mathcal{L}$ on $A$ which is invertible (locally isomorphic to the unit), admits a projective presentation by sections over $\operatorname{Spec} S$ whose associated morphism to projective space is a closed immersion, and whose geometric fibre $H^0$ has $k$-dimension $d$ for every algebraically closed field $k$ and every map $S \to k$. The conclusion is that there exists a polarised abelian scheme $u'$ of the same type $(g,d,n)$ over $S'$ which is a base change of $u$ along $\varphi$ in the sense of `PolarisedAbelianScheme.IsPullback`: there is a morphism $g_A : u'.A \to u.A$ making $u'.f$, $u.f$ and $\operatorname{Spec}\varphi$ into a pullback square, such that $g_A$ carries the group law of $u'$ to that of $u$ on points over every test scheme, sends each section $P'_i$ of $u'$ to the composite of $\operatorname{Spec}\varphi$ with $P_i$, and pulls $u.\mathcal{L}$ back to a module isomorphic to $u'.\mathcal{L}$.
--
--   This is the existence half of the base-change formalism for polarised abelian schemes with full level-$n$ structure: the relation `IsPullback` between such data over $S$ and over $S'$ is always inhabited on the target side, so that a polarised abelian scheme may be transported along an arbitrary ring map. It is used by the results on quaternionic multiplication structures on polarised abelian schemes, where objects defined over one base must be compared with their reductions and localisations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_PolarisedAbelianScheme_exists_isPullback.lean

import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.PolarisedAbelianScheme

theorem AlgebraicGeometry.PolarisedAbelianScheme.exists_isPullback
    {g d n : ℕ} {S S' : Type} [CommRing S] [CommRing S'] (φ : S →+* S')
    (u : PolarisedAbelianScheme g d n S) :
    ∃ u' : PolarisedAbelianScheme g d n S', PolarisedAbelianScheme.IsPullback φ u u' := by sorry
