-- Prove2me | Theorems.Thm_AlgebraicGeometry_existsUnique_specMap_mk_pow_comp_eq_of_isAdicComplete_of_isLocalRing
-- name    : AlgebraicGeometry.existsUnique_specMap_mk_pow_comp_eq_of_isAdicComplete_of_isLocalRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.195734+00:00
-- url     : https://prove2.me/theorems/d773e300-e164-5506-bffc-ad1249b58fd9
-- title:
--   S-points of a scheme from compatible points modulo Iⁿ⁺¹
-- statement:
--   Let $S$ be a commutative ring that is local, let $I \subseteq S$ be an ideal, and assume $S$ is $I$-adically complete (complete and separated for the $I$-adic topology, in the sense of Mathlib's `IsAdicComplete`). Let $X$ be an arbitrary scheme. Suppose given, for each natural number $n$, a morphism of schemes $x_n \colon \operatorname{Spec}(S/I^{n+1}) \to X$, and suppose this family is compatible with the transition maps: for every $n$, the morphism $\operatorname{Spec}(S/I^{n+1}) \to \operatorname{Spec}(S/I^{n+2})$ induced by the canonical surjection $S/I^{n+2} \to S/I^{n+1}$, followed by $x_{n+1}$, equals $x_n$. The conclusion is that there is exactly one morphism of schemes $y \colon \operatorname{Spec} S \to X$ such that for every $n$ the morphism $\operatorname{Spec}(S/I^{n+1}) \to \operatorname{Spec} S$ induced by the quotient map $S \to S/I^{n+1}$, followed by $y$, equals $x_n$. Equivalently, the natural map $X(S) \to \varprojlim_n X(S/I^{n+1})$ is a bijection for such $S$; all rings and schemes live in a single universe.
--
--   This is the statement that for a complete local ring $S$ the formal spectrum of $S$ has the same morphisms into a scheme $X$ as $\operatorname{Spec} S$ itself, i.e. $\operatorname{Hom}(\operatorname{Spf} S, X) = X(S)$; it rests on the fact that a morphism from the spectrum of a local ring into $X$ factors through any open neighbourhood of the image of the closed point. It is used in the Čerednik–Drinfel'd part of the development, where compatible families of points modulo powers of an ideal are assembled into a single point of a scheme.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_existsUnique_specMap_mk_pow_comp_eq_of_isAdicComplete_of_isLocalRing.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

universe u

theorem AlgebraicGeometry.existsUnique_specMap_mk_pow_comp_eq_of_isAdicComplete_of_isLocalRing
    {S : Type u} [CommRing S] [IsLocalRing S] (I : Ideal S) [IsAdicComplete I S] {X : Scheme.{u}}
    (x : ∀ n : ℕ, Spec (CommRingCat.of (S ⧸ I ^ (n + 1))) ⟶ X)
    (hx : ∀ n : ℕ,
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.factorPowSucc I (n + 1))) ≫ x (n + 1) = x n) :
    ∃! y : Spec (CommRingCat.of S) ⟶ X,
      ∀ n : ℕ, Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1)))) ≫ y = x n := by sorry
