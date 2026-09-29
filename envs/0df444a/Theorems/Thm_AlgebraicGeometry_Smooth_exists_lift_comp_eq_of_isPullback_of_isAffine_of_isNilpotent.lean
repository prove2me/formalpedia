-- Prove2me | Theorems.Thm_AlgebraicGeometry_Smooth_exists_lift_comp_eq_of_isPullback_of_isAffine_of_isNilpotent
-- name    : AlgebraicGeometry.Smooth.exists_lift_comp_eq_of_isPullback_of_isAffine_of_isNilpotent
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.655938+00:00
-- url     : https://prove2.me/theorems/5601e59a-75c8-5bd7-b768-d82fc8be5d1c
-- title:
--   Infinitesimal lifting of morphisms into a smooth affine scheme
-- statement:
--   Let $\pi \colon T' \to T$ be a surjective homomorphism of commutative rings whose kernel is a nilpotent ideal (some power of $\ker \pi$ is zero). Consider schemes $Z$ and $V$ with a morphism $q_Z \colon Z \to \operatorname{Spec} T'$, with $Z$ affine, together with $g_Z \colon V \to Z$ and $f_V \colon V \to \operatorname{Spec} T$ forming a pullback square over $\operatorname{Spec}\pi$, so that $g_Z$ followed by $q_Z$ equals $f_V$ followed by $\operatorname{Spec}\pi$ and $V$ is the fibre product $Z \times_{\operatorname{Spec} T'} \operatorname{Spec} T$. Likewise let $q \colon Y \to \operatorname{Spec} T'$ be a smooth morphism with $Y$ affine, and let $g \colon U \to Y$, $f_U \colon U \to \operatorname{Spec} T$ exhibit $U$ as the pullback of $Y$ along $\operatorname{Spec}\pi$. Finally let $h \colon V \to U$ be a morphism over $\operatorname{Spec} T$, i.e. $h$ followed by $f_U$ equals $f_V$. The conclusion asserts the existence of a morphism $h_Z \colon Z \to Y$ which is a morphism over $\operatorname{Spec} T'$, in that $h_Z$ followed by $q$ equals $q_Z$, and which lifts $h$, in that $g_Z$ followed by $h_Z$ equals $h$ followed by $g$. No uniqueness of $h_Z$ is claimed.
--
--   This is the infinitesimal lifting criterion for smooth morphisms: morphisms into a smooth affine $T'$-scheme extend across the nilpotent thickening $\operatorname{Spec} T \hookrightarrow \operatorname{Spec} T'$, in the affine case where it reduces to the formal smoothness of the corresponding algebra. It is used in the construction of good reduction data for Jacobians, both in the regluing of bare deformations and in assembling local lifts of the group law.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Smooth_exists_lift_comp_eq_of_isPullback_of_isAffine_of_isNilpotent.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.Smooth.exists_lift_comp_eq_of_isPullback_of_isAffine_of_isNilpotent
    {T' T : Type u} [CommRing T'] [CommRing T] (π : T' →+* T) (hπ : Function.Surjective π)
    (hker : IsNilpotent (RingHom.ker π))
    {Z V : Scheme.{u}} (qZ : Z ⟶ Spec (CommRingCat.of T')) [IsAffine Z]
    (gZ : V ⟶ Z) (fV : V ⟶ Spec (CommRingCat.of T)) (hgZ : IsPullback gZ fV qZ (Spec.map (CommRingCat.ofHom π)))
    {Y U : Scheme.{u}} (q : Y ⟶ Spec (CommRingCat.of T')) [IsAffine Y] [Smooth q]
    (g : U ⟶ Y) (fU : U ⟶ Spec (CommRingCat.of T)) (hg : IsPullback g fU q (Spec.map (CommRingCat.ofHom π)))
    (h : V ⟶ U) (hh : h ≫ fU = fV) :
    ∃ hZ : Z ⟶ Y, hZ ≫ q = qZ ∧ gZ ≫ hZ = h ≫ g := by sorry
