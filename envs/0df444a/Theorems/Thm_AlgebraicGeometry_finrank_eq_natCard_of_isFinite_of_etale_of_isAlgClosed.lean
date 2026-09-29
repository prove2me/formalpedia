-- Prove2me | Theorems.Thm_AlgebraicGeometry_finrank_eq_natCard_of_isFinite_of_etale_of_isAlgClosed
-- name    : AlgebraicGeometry.finrank_eq_natCard_of_isFinite_of_etale_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.96328+00:00
-- url     : https://prove2.me/theorems/b65efbe0-51f0-5a9c-b2a4-7ecf5c5ed0bc
-- title:
--   Rank of a finite étale morphism at a geometric point
-- statement:
--   Let $S$ be a commutative ring, let $W$ be a scheme and let $q : W \to \operatorname{Spec} S$ be a morphism that is finite and étale (both as typeclass hypotheses). Let $k$ be an algebraically closed field and let $s_k : S \to k$ be a ring homomorphism; write $\iota = \operatorname{Spec}(s_k) : \operatorname{Spec} k \to \operatorname{Spec} S$ for the induced morphism of schemes and let $\bar s$ be the image under the underlying map of $\iota$ of the closed point of $\operatorname{Spec} k$ (that is, the prime ideal $\ker(s_k)$ of $S$). The assertion is the equality of natural numbers $$\operatorname{finrank}_{\bar s}(q) \;=\; \#\{\, w : \operatorname{Spec} k \to W \;:\; w \text{ followed by } q \,=\, \iota \,\},$$ where the left-hand side is the rank of $q$ at the point $\bar s$ in the sense of `Scheme.Hom.finrank`, and the right-hand side is the cardinality (as a `Nat.card`, hence $0$ if the set were infinite, which it is not here) of the set of $k$-points of $W$ whose composite with $q$ is exactly $\iota$, i.e. of the geometric points of the fibre of $q$ over the geometric point $s_k$.
--
--   This is the classical statement that a finite étale morphism has, at each geometric point, rank equal to the number of points of the corresponding geometric fibre. It is used in the Čerednik–Drinfel'd part of the development to convert rank statements about finite étale covers (clopen pieces of torsion of abelian schemes, and the representability of extra level structures) into counts of geometric points.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_finrank_eq_natCard_of_isFinite_of_etale_of_isAlgClosed.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.finrank_eq_natCard_of_isFinite_of_etale_of_isAlgClosed
    {S : Type u} [CommRing S] {W : Scheme.{u}} (q : W ⟶ Spec (CommRingCat.of S)) [IsFinite q] [Etale q]
    (k : Type u) [Field k] [IsAlgClosed k] (sk : S →+* k) :
    q.finrank (Spec.map (CommRingCat.ofHom sk) (IsLocalRing.closedPoint k)) =
      Nat.card {w : Spec (CommRingCat.of k) ⟶ W // w ≫ q = Spec.map (CommRingCat.ofHom sk)} := by sorry
