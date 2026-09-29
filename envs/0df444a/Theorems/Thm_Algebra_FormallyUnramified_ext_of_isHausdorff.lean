-- Prove2me | Theorems.Thm_Algebra_FormallyUnramified_ext_of_isHausdorff
-- name    : Algebra.FormallyUnramified.ext_of_isHausdorff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.846094+00:00
-- url     : https://prove2.me/theorems/d79e1662-52d4-52e0-932e-fd93b25fb7e8
-- title:
--   Uniqueness of formally unramified maps into I-adically separated rings
-- statement:
--   Let $R$, $A$, $B$ be commutative rings with $A$ and $B$ both $R$-algebras, and suppose $A$ is formally unramified over $R$ in Mathlib's sense (uniqueness of lifts of $R$-algebra maps along surjections with nilpotent kernel). Let $I$ be an ideal of $B$ such that $B$ is Hausdorff for the $I$-adic filtration, i.e. an element of $B$ congruent to $0$ modulo $I^n \cdot B$ for every $n$ is $0$; equivalently $\bigcap_n I^n = 0$. Let $f, g \colon A \to B$ be $R$-algebra homomorphisms whose composites with the quotient map $B \to B/I$ agree, that is, $f$ and $g$ agree modulo $I$. The conclusion is that $f = g$. This is the $I$-adically separated analogue of Mathlib's `Algebra.FormallyUnramified.lift_unique`, which instead requires the ideal to be nilpotent.
--
--   This is the standard uniqueness half of formal unramifiedness, extended from nilpotent thickenings to $I$-adically separated (Hausdorff) targets. It is used in the étale-local theory of this development, namely in [`Algebra.Etale.exists_algEquiv_residue_eq_of_isLocalRing_of_isAdicComplete`](thm.html#Algebra.Etale.exists_algEquiv_residue_eq_of_isLocalRing_of_isAdicComplete), where an algebra map into a complete local ring is pinned down by its reduction.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Algebra_FormallyUnramified_ext_of_isHausdorff.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem Algebra.FormallyUnramified.ext_of_isHausdorff (R A B : Type*) [CommRing R] [CommRing A] [Algebra R A]
    [CommRing B] [Algebra R B]
    [Algebra.FormallyUnramified R A] (I : Ideal B) [IsHausdorff I B] (f g : A →ₐ[R] B)
    (h : (Ideal.Quotient.mkₐ R I).comp f = (Ideal.Quotient.mkₐ R I).comp g) : f = g := by sorry
