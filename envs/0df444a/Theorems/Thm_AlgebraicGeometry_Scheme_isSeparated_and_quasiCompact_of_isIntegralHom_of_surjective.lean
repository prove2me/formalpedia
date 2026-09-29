-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_isSeparated_and_quasiCompact_of_isIntegralHom_of_surjective
-- name    : AlgebraicGeometry.Scheme.isSeparated_and_quasiCompact_of_isIntegralHom_of_surjective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.322128+00:00
-- url     : https://prove2.me/theorems/d29e473c-e594-57b5-839d-2c8404975e0d
-- title:
--   Separatedness and quasi-compactness descend along integral surjections
-- statement:
--   Let $B$ be a commutative ring and let $M$, $X$ be schemes, with morphisms $\pi_M : M \to \operatorname{Spec} B$, $\pi_X : X \to \operatorname{Spec} B$ and $\pi : M \to X$ such that $\pi$ followed by $\pi_X$ equals $\pi_M$. Assume that $\pi$ is an integral morphism (`IsIntegralHom`), that the continuous map of underlying topological spaces induced by $\pi$ is surjective, and that $\pi_M$ is separated (its diagonal $M \to M \times_{\operatorname{Spec} B} M$ is a closed immersion) and quasi-compact (preimages under $\pi_M$ of compact open subsets of $\operatorname{Spec} B$ are compact). The conclusion is the conjunction of the corresponding two properties for $\pi_X$: the diagonal of $\pi_X$ is a closed immersion, and $\pi_X$ is quasi-compact. Thus the structure morphism of the target of an integral surjection inherits separatedness and quasi-compactness from that of the source; no finiteness or quasi-compactness hypothesis on $X$ itself, and no reducedness or Noetherian hypothesis, is imposed.
--
--   This is the descent of separatedness and quasi-compactness over a base along an integral surjective morphism, in the form in which these properties are checked for a quotient scheme once they are known for the scheme being quotiented. It is used in the construction of coarse moduli schemes in the Čerednik–Drinfel'd setting, where $\pi$ is the quotient map from a fine moduli scheme, and in the companion statement for quotients by finite group actions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_isSeparated_and_quasiCompact_of_isIntegralHom_of_surjective.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory

universe u

theorem AlgebraicGeometry.Scheme.isSeparated_and_quasiCompact_of_isIntegralHom_of_surjective
    {B : Type u} [CommRing B] {M X : Scheme.{u}} (πM : M ⟶ Spec (CommRingCat.of B))
    (πX : X ⟶ Spec (CommRingCat.of B)) (π : M ⟶ X) (hπX : π ≫ πX = πM)
    (hint : IsIntegralHom π) (hsurj : Function.Surjective π.base)
    (hsep : IsSeparated πM) (hqc : QuasiCompact πM) :
    IsSeparated πX ∧ QuasiCompact πX := by sorry
