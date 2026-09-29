-- Prove2me | Theorems.Thm_AlgebraicGeometry_isClosedImmersion_and_isProper_and_smooth_of_isPullback_specMap_of_surjective_of_isNilpotent_ker
-- name    : AlgebraicGeometry.isClosedImmersion_and_isProper_and_smooth_of_isPullback_specMap_of_surjective_of_isNilpotent_ker
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.96328+00:00
-- url     : https://prove2.me/theorems/ed3feb63-c1d8-5728-a244-ee650da761f3
-- title:
--   Descent of properties along a nilpotent thickening of the base
-- statement:
--   Let $\pi : P \to B'$ be a homomorphism of commutative rings which is surjective and whose kernel is a nilpotent ideal. Let $X$ and $X'$ be schemes, and let $f : X \to \operatorname{Spec} P$, $f' : X' \to \operatorname{Spec} B'$ and $k' : X' \to X$ be morphisms of schemes such that the square formed by $k'$, $f'$, $f$ and $\operatorname{Spec}(\pi) : \operatorname{Spec} B' \to \operatorname{Spec} P$ is a pullback square, i.e. $X'$ together with $k'$ and $f'$ is a fibre product of $X$ and $\operatorname{Spec} B'$ over $\operatorname{Spec} P$. The conclusion is a conjunction of four assertions: first, $k'$ is a closed immersion and the underlying map of topological spaces of $k'$ is bijective; second, if $f'$ is locally of finite type then so is $f$; third, if $f'$ is proper then so is $f$; and fourth, if $f$ is flat and locally of finite presentation and $f'$ is smooth, then $f$ is smooth.
--
--   This is the standard transfer of closed-immersion, finite-type, properness and smoothness properties across a nilpotent thickening $\operatorname{Spec} B' \hookrightarrow \operatorname{Spec} P$ of an affine base, in the descending direction (from the closed fibre to the thickening). It is used in the construction of schemes over a ring obtained by gluing along such a thickening, in [`AlgebraicGeometry.exists_isPushout_isPullback_specMap_pullbackFst_pullbackSnd_of_surjective_of_isNilpotent`](thm.html#AlgebraicGeometry.exists_isPushout_isPullback_specMap_pullbackFst_pullbackSnd_of_surjective_of_isNilpotent).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_isClosedImmersion_and_isProper_and_smooth_of_isPullback_specMap_of_surjective_of_isNilpotent_ker.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.isClosedImmersion_and_isProper_and_smooth_of_isPullback_specMap_of_surjective_of_isNilpotent_ker
    {P B' : Type} [CommRing P] [CommRing B'] (π : P →+* B')
    (hπs : Function.Surjective π) (hπn : IsNilpotent (RingHom.ker π))
    {X X' : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of P)) (f' : X' ⟶ Spec (CommRingCat.of B'))
    (k' : X' ⟶ X) (hk : IsPullback k' f' f (Spec.map (CommRingCat.ofHom π))) :
    (IsClosedImmersion k' ∧ Function.Bijective k'.base) ∧
    (LocallyOfFiniteType f' → LocallyOfFiniteType f) ∧
    (IsProper f' → IsProper f) ∧
    (Flat f → LocallyOfFinitePresentation f → Smooth f' → Smooth f) := by sorry
