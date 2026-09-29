-- Prove2me | Theorems.Thm_AlgebraicGeometry_IsClosedImmersion_exists_ideal_forall_exists_comp_eq_specMap_iff_forall_map_eq_zero
-- name    : AlgebraicGeometry.IsClosedImmersion.exists_ideal_forall_exists_comp_eq_specMap_iff_forall_map_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.268945+00:00
-- url     : https://prove2.me/theorems/ef7d5445-7d42-56c6-aa51-15b89f233aad
-- title:
--   Closed subschemes of an affine scheme are cut out by an ideal
-- statement:
--   Let $S$ be a commutative ring (in a fixed universe), let $Z$ be a scheme, and let $\iota : Z \to \operatorname{Spec} S$ be a morphism of schemes that is a closed immersion. The assertion is that there exists an ideal $J \subseteq S$ with the following property: for every commutative ring $R$ in the same universe and every ring homomorphism $\varphi : S \to R$, there exists a morphism $y : \operatorname{Spec} R \to Z$ with $y$ followed by $\iota$ equal to $\operatorname{Spec}\varphi$ if and only if $\varphi(x) = 0$ for every $x \in J$. Thus the $S$-points of the closed subscheme $Z$ with values in affine schemes are precisely those $\varphi$ killing $J$. Only existence of a factorisation is asserted, not its uniqueness, and the ideal $J$ is produced existentially (the proof takes $J$ to be the kernel of the induced map $S \to \Gamma(Z, \mathcal{O}_Z)$); the statement is formulated solely for affine test schemes $\operatorname{Spec} R$.
--
--   This is the functor-of-points formulation of the classical fact that a closed subscheme of $\operatorname{Spec} S$ is $\operatorname{Spec}(S/J)$ for an ideal $J$, so that a map $\operatorname{Spec} R \to \operatorname{Spec} S$ factors through it exactly when the corresponding ring map annihilates $J$. It is used in the project to obtain ideals cutting out closed conditions on affine parameter schemes, for instance via [`AlgebraicGeometry.exists_ideal_forall_exists_comp_eq_specMap_comp_iff_le_ker_of_isClosedImmersion`](thm.html#AlgebraicGeometry.exists_ideal_forall_exists_comp_eq_specMap_comp_iff_le_ker_of_isClosedImmersion) and in the construction of ideals characterising Rosati-compatibility after base change for bundles of abelian-scheme properties.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_IsClosedImmersion_exists_ideal_forall_exists_comp_eq_specMap_iff_forall_map_eq_zero.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.IsClosedImmersion.exists_ideal_forall_exists_comp_eq_specMap_iff_forall_map_eq_zero
    {S : Type u} [CommRing S] {Z : Scheme.{u}} (ι : Z ⟶ Spec (CommRingCat.of S)) [IsClosedImmersion ι] :
    ∃ J : Ideal S, ∀ (R : Type u) [CommRing R] (φ : S →+* R),
      (∃ y : Spec (CommRingCat.of R) ⟶ Z, y ≫ ι = Spec.map (CommRingCat.ofHom φ)) ↔ ∀ x ∈ J, φ x = 0 := by sorry
