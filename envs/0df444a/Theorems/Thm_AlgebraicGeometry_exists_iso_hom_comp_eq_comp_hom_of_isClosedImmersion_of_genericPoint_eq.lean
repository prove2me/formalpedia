-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_iso_hom_comp_eq_comp_hom_of_isClosedImmersion_of_genericPoint_eq
-- name    : AlgebraicGeometry.exists_iso_hom_comp_eq_comp_hom_of_isClosedImmersion_of_genericPoint_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.552687+00:00
-- url     : https://prove2.me/theorems/a7845320-104a-5b62-b693-b4534777bc0f
-- title:
--   Automorphism fixing the generic point restricts to the closed subscheme
-- statement:
--   Let $S$, $Z$, $C$ be schemes, $q\colon Z\to S$ and $c\colon C\to S$ morphisms, and $i\colon C\to Z$ a closed immersion with $C$ integral (irreducible and reduced), so that $C$ has a generic point $\eta$. Assume $i$ is a morphism over $S$, i.e. $i$ followed by $q$ equals $c$, and let $g$ be an isomorphism $Z\cong Z$ over $S$, i.e. $g.\mathrm{hom}$ followed by $q$ equals $q$, whose underlying continuous map fixes the image of the generic point: $g.\mathrm{hom}$ sends $i(\eta)$ to $i(\eta)$. The conclusion is that there exists an isomorphism $\alpha\colon C\cong C$ such that $\alpha.\mathrm{hom}$ followed by $c$ equals $c$ (so $\alpha$ is an automorphism of $C$ over $S$) and $\alpha.\mathrm{hom}$ followed by $i$ equals $i$ followed by $g.\mathrm{hom}$; that is, $\alpha$ is an automorphism of $C$ over $S$ compatible with $g$ along the closed immersion $i$.
--
--   This is the standard statement that an automorphism of an ambient scheme which preserves the generic point of an integral closed subscheme restricts to an automorphism of that subscheme, the restriction being unique because the subscheme is reduced. It is used in the analysis of the special fibre of the model of $X_1(Mp)$, to restrict diamond automorphisms to the individual Igusa components once they are known to fix the generic point of the component.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_exists_iso_hom_comp_eq_comp_hom_of_isClosedImmersion_of_genericPoint_eq.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.exists_iso_hom_comp_eq_comp_hom_of_isClosedImmersion_of_genericPoint_eq
    {S Z C : Scheme.{u}} (q : Z ⟶ S) (c : C ⟶ S) (i : C ⟶ Z) [IsClosedImmersion i] [IsIntegral C]
    (hi : i ≫ q = c) (g : Z ≅ Z) (hg : g.hom ≫ q = q)
    (hfix : g.hom.base (i.base (genericPoint C)) = i.base (genericPoint C)) :
    ∃ α : C ≅ C, α.hom ≫ c = c ∧ α.hom ≫ i = i ≫ g.hom := by sorry
