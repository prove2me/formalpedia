-- Prove2me | Theorems.Thm_AlgebraicGeometry_isIso_morphismRestrict_of_isOpenImmersion_of_range_eq
-- name    : AlgebraicGeometry.isIso_morphismRestrict_of_isOpenImmersion_of_range_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.489634+00:00
-- url     : https://prove2.me/theorems/3c3d71ce-ee74-5923-8716-5fbd49560caa
-- title:
--   Section that is an open immersion onto the preimage
-- statement:
--   Let $P$ and $P'$ be schemes, $\beta : P' \to P$ a morphism, $U$ an open subscheme of $P$, and $s : U \to P'$ a morphism from $U$ (regarded as a scheme) to $P'$ which is an open immersion. Assume two compatibilities: first, $s$ followed by $\beta$ equals the canonical open immersion $U \hookrightarrow P$, so that $s$ is a section of $\beta$ over $U$; second, the image of the underlying continuous map of $s$ is exactly the preimage $\beta^{-1}(U)$ of the underlying set of $U$ under the underlying map of $\beta$. The conclusion is that the restricted morphism $\beta \mid_U$, that is the induced morphism from the open subscheme $\beta^{-1}(U)$ of $P'$ to $U$ obtained from $\beta$ by base change along $U \hookrightarrow P$, is an isomorphism of schemes.
--
--   This is the standard criterion that a morphism admitting a section over an open $U$ whose image fills out the whole preimage of $U$ is an isomorphism above $U$. It is used in the construction of a proper morphism which is an isomorphism over the locus where the stalk has Krull dimension one.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_isIso_morphismRestrict_of_isOpenImmersion_of_range_eq.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

universe u

theorem AlgebraicGeometry.isIso_morphismRestrict_of_isOpenImmersion_of_range_eq
    {P P' : Scheme.{u}} (β : P' ⟶ P) (U : P.Opens) (s : (U : Scheme.{u}) ⟶ P') [IsOpenImmersion s]
    (hsβ : s ≫ β = U.ι) (hsr : Set.range s.base = β.base ⁻¹' (U : Set P)) :
    IsIso (β ∣_ U) := by sorry
