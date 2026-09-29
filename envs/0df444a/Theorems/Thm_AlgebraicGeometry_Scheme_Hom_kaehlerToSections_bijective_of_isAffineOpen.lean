-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Hom_kaehlerToSections_bijective_of_isAffineOpen
-- name    : AlgebraicGeometry.Scheme.Hom.kaehlerToSections_bijective_of_isAffineOpen
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.223894+00:00
-- url     : https://prove2.me/theorems/c5712e75-8afb-5c77-ab2c-67b1ccd1c621
-- title:
--   Sheafification does not change differentials on affine opens
-- statement:
--   Let $A$ be a commutative ring, let $X$ be a scheme and let $f \colon X \to \operatorname{Spec} A$ be a morphism of schemes, where $\operatorname{Spec} A$ is the spectrum of $A$ viewed as an object of the category of commutative rings. Let $U$ be an open subscheme of $X$ and assume that $U$ is an affine open of $X$. Consider the presheaf of $\mathcal{O}_X$-modules $f.\,$`kaehlerPresheaf` of relative differentials of $f$, obtained from the map of presheaves of rings underlying $f$ by the relative differentials construction for presheaves of modules, and its sheafification $f.\,$`kaehler` with respect to the identity of the sheaf of rings $\mathcal{O}_X$. The map `f.kaehlerToSections U` is the component at the open $U$ of the unit of the sheafification adjunction, a map from the $\Gamma(U,\mathcal{O}_X)$-module of sections of the presheaf of differentials over $U$ to the module $\Gamma(f.\,$`kaehler`$, U)$ of sections over $U$ of the sheafified module. The assertion is that this map is bijective as a map of types.
--
--   This is the affine comparison statement $\Omega_{B/A} \cong \Gamma(U, \Omega^1_{X/A})$ for $U$ affine open with $B = \Gamma(U,\mathcal{O}_X)$: the presheaf of Kähler differentials already has the correct sections over an affine open, so sheafification does not alter them. It is the bridge used to compute differential forms on affine charts, and is cited in the construction of bases of differentials on affine opens of smooth morphisms of relative dimension one and in the recognition of frames and isomorphisms of the sheaf of differentials along pullbacks.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Hom_kaehlerToSections_bijective_of_isAffineOpen.lean

import Mathlib
import Definitions.Def_PresheafOfModules_ExteriorPower
import Definitions.Def_AlgebraicGeometry_ModulesDet
import Definitions.Def_AlgebraicGeometry_KaehlerModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory Opposite AlgebraicGeometry

universe u

theorem AlgebraicGeometry.Scheme.Hom.kaehlerToSections_bijective_of_isAffineOpen
    {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A))
    {U : X.Opens} (hU : IsAffineOpen U) :
    Function.Bijective (f.kaehlerToSections U) := by sorry
