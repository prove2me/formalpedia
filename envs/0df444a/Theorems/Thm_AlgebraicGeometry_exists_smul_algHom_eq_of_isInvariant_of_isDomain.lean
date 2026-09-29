-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_smul_algHom_eq_of_isInvariant_of_isDomain
-- name    : AlgebraicGeometry.exists_smul_algHom_eq_of_isInvariant_of_isDomain
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.96328+00:00
-- url     : https://prove2.me/theorems/fe84b764-95ba-5eda-a5bb-a168d9040dfd
-- title:
--   Two A-algebra maps from D into a domain differ by G
-- statement:
--   Let $A$ and $D$ be commutative rings with $D$ an $A$-algebra, and let $G$ be a finite group acting on $D$ by ring automorphisms (a `MulSemiringAction`) in a way that commutes with the $A$-action on $D$, and such that `Algebra.IsInvariant A D G` holds, i.e. every $G$-invariant element of $D$ lies in the image of $A \to D$. Let $R$ be a commutative ring that is an integral domain and an $A$-algebra. Then for any two $A$-algebra homomorphisms $s, s' : D \to R$ there exists $g \in G$ with $s'(d) = s(g \cdot d)$ for all $d \in D$. Note that $g$ is produced uniformly for all $d$ (the quantifier over $d$ is inside the existential), and that no finiteness, flatness or integrality hypothesis on $D$ over $A$ beyond invariance is imposed; the only hypothesis on the target is that it is a domain, so in particular $s$ and $s'$ need not be surjective or injective.
--
--   This is the classical statement that two points of $\operatorname{Spec} D$ with values in a domain which agree over $A = D^G$ are conjugate under $G$ (Bourbaki, Algèbre commutative V §2: primes of $D$ above a given prime of $A$ form a single $G$-orbit, together with surjectivity of the decomposition group onto the residue automorphisms). It is used in the construction of the finite-group quotient of a flat proper adic tower, via [`AlgebraicGeometry.nonempty_towerQuotientDatum_of_isProper_of_flat_of_forall_exists_isAffineOpen`](thm.html#AlgebraicGeometry.nonempty_towerQuotientDatum_of_isProper_of_flat_of_forall_exists_isAffineOpen), to obtain uniqueness up to $G$ of lifts of points through the quotient projection.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_exists_smul_algHom_eq_of_isInvariant_of_isDomain.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem AlgebraicGeometry.exists_smul_algHom_eq_of_isInvariant_of_isDomain
    (A : Type) [CommRing A] (D : Type) [CommRing D] [Algebra A D]
    (G : Type) [Group G] [Finite G] [MulSemiringAction G D] [SMulCommClass G A D] [Algebra.IsInvariant A D G]
    (R : Type) [CommRing R] [IsDomain R] [Algebra A R]
    (s s' : D →ₐ[A] R) :
    ∃ g : G, ∀ d : D, s' d = s (g • d) := by sorry
