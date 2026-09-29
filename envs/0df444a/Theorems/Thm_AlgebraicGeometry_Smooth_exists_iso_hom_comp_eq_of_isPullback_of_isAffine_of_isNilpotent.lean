-- Prove2me | Theorems.Thm_AlgebraicGeometry_Smooth_exists_iso_hom_comp_eq_of_isPullback_of_isAffine_of_isNilpotent
-- name    : AlgebraicGeometry.Smooth.exists_iso_hom_comp_eq_of_isPullback_of_isAffine_of_isNilpotent
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.655938+00:00
-- url     : https://prove2.me/theorems/0686c965-f065-51f6-a26a-6480e29781ca
-- title:
--   Uniqueness of affine smooth lifts along a nilpotent thickening
-- statement:
--   Let $T'$ and $T$ be commutative rings and $\pi\colon T'\to T$ a surjective ring homomorphism whose kernel is a nilpotent ideal. Let $V$, $Y$, $Y'$ be schemes, $v\colon V\to\operatorname{Spec} T$ an arbitrary morphism, and let $q\colon Y\to\operatorname{Spec} T'$ and $q'\colon Y'\to\operatorname{Spec} T'$ be smooth morphisms with $Y$ and $Y'$ affine schemes. Suppose given morphisms $g\colon V\to Y$ and $g'\colon V\to Y'$ such that both squares
--   $$\begin{array}{ccc} V & \xrightarrow{g} & Y\\ \downarrow v & & \downarrow q\\ \operatorname{Spec} T & \xrightarrow{\operatorname{Spec}\pi} & \operatorname{Spec} T'\end{array}$$
--   and the analogous square for $g'$, $q'$ are cartesian, i.e. exhibit $V$ as the base change of $Y$, respectively $Y'$, along $\operatorname{Spec}\pi$. The conclusion is that $Y$ and $Y'$ are isomorphic as lifts of $V$: there exists an isomorphism of schemes $\varphi\colon Y\xrightarrow{\ \sim\ }Y'$ with $\varphi$ followed by $q'$ equal to $q$, and $g$ followed by $\varphi$ equal to $g'$. (Here all rings and schemes live in a single universe, and $\operatorname{Spec}$ is applied to the commutative rings regarded as objects of `CommRingCat`.)
--
--   This is the scheme-theoretic uniqueness statement for smooth lifts across a nilpotent thickening of affine bases, in the affine case: the classical infinitesimal lifting criterion for smoothness (SGA 1, Exp. III, 6.8; Stacks project tag 08UZ), obtained here from the formally smooth algebra statement [`Algebra.FormallySmooth.exists_algEquiv_comp_eq_of_isNilpotent_of_ker_eq_map`](thm.html#Algebra.FormallySmooth.exists_algEquiv_comp_eq_of_isNilpotent_of_ker_eq_map) by passing to the coordinate rings of $Y$, $Y'$ and $V$. It is used by [`AlgebraicGeometry.Smooth.exists_overlap_isos_local_lifts`](thm.html#AlgebraicGeometry.Smooth.exists_overlap_isos_local_lifts) as the local input to the patching of lifts over an affine open cover.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Smooth_exists_iso_hom_comp_eq_of_isPullback_of_isAffine_of_isNilpotent.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme.TwoAffineOpenCover

universe u

theorem AlgebraicGeometry.Smooth.exists_iso_hom_comp_eq_of_isPullback_of_isAffine_of_isNilpotent
    {T' T : Type u} [CommRing T'] [CommRing T] (π : T' →+* T) (hπ : Function.Surjective π)
    (hker : IsNilpotent (RingHom.ker π))
    {V Y Y' : Scheme.{u}} (v : V ⟶ Spec (CommRingCat.of T))
    (q : Y ⟶ Spec (CommRingCat.of T')) [IsAffine Y] (hq : Smooth q)
    (q' : Y' ⟶ Spec (CommRingCat.of T')) [IsAffine Y'] (hq' : Smooth q')
    (g : V ⟶ Y) (hg : IsPullback g v q (Spec.map (CommRingCat.ofHom π)))
    (g' : V ⟶ Y') (hg' : IsPullback g' v q' (Spec.map (CommRingCat.ofHom π))) :
    ∃ φ : Y ≅ Y', φ.hom ≫ q' = q ∧ g ≫ φ.hom = g' := by sorry
