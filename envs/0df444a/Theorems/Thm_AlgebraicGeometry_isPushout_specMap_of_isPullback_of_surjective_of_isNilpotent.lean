-- Prove2me | Theorems.Thm_AlgebraicGeometry_isPushout_specMap_of_isPullback_of_surjective_of_isNilpotent
-- name    : AlgebraicGeometry.isPushout_specMap_of_isPullback_of_surjective_of_isNilpotent
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.489634+00:00
-- url     : https://prove2.me/theorems/81a2c80f-dd27-595e-8a6e-869553ee6f57
-- title:
--   Spec of a ring fibre product along a nilpotent thickening is a pushout of schemes
-- statement:
--   Let $R$, $C$, $C'$, $C_0$ be commutative rings (objects of `CommRingCat` in a fixed universe) and let $\mathrm{fst} : R \to C$, $\mathrm{snd} : R \to C'$, $q : C \to C_0$, $q' : C' \to C_0$ be ring homomorphisms. Assume that the square formed by these four maps is a pullback square in `CommRingCat`, so that $R$ together with $\mathrm{fst}$ and $\mathrm{snd}$ is the fibre product $C \times_{C_0} C'$; assume further that the underlying ring homomorphism of $q'$ is surjective and that every element of its kernel is nilpotent (each element individually, with no uniform bound on the exponent). The conclusion is that applying $\operatorname{Spec}$ turns this square into a pushout square of schemes: the square with $\operatorname{Spec} q : \operatorname{Spec} C_0 \to \operatorname{Spec} C$ and $\operatorname{Spec} q' : \operatorname{Spec} C_0 \to \operatorname{Spec} C'$ as the two maps out of $\operatorname{Spec} C_0$, and $\operatorname{Spec}\mathrm{fst}$, $\operatorname{Spec}\mathrm{snd}$ as the two maps into $\operatorname{Spec} R$, satisfies `IsPushout` in the category of schemes. In particular $\operatorname{Spec} R$ represents the pushout of $\operatorname{Spec} C \leftarrow \operatorname{Spec} C_0 \to \operatorname{Spec} C'$ against arbitrary, possibly non-affine, target schemes.
--
--   This is the standard gluing (pinching) statement that $\operatorname{Spec}$ carries a cartesian square of rings with one leg a surjection with nilpotent kernel to a pushout of schemes, the scheme-theoretic counterpart of the fibre-product construction used in deformation theory. It is used in the project for the analysis of small extensions and tangent spaces of deformation functors, where it supplies the extension and uniqueness of morphisms out of $\operatorname{Spec}$ of a ring fibre product.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_isPushout_specMap_of_isPullback_of_surjective_of_isNilpotent.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.isPushout_specMap_of_isPullback_of_surjective_of_isNilpotent
    {R C C' C₀ : CommRingCat.{u}} {fst : R ⟶ C} {snd : R ⟶ C'} {q : C ⟶ C₀} {q' : C' ⟶ C₀}
    (H : IsPullback fst snd q q') (hq' : Function.Surjective q'.hom)
    (hnil : ∀ x ∈ RingHom.ker q'.hom, IsNilpotent x) :
    IsPushout (Spec.map q) (Spec.map q') (Spec.map fst) (Spec.map snd) := by sorry
