-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_exists_iso_comp_homOfLE_eq_homOfLE_comp_of_preimage_eq
-- name    : AlgebraicGeometry.Scheme.exists_iso_comp_homOfLE_eq_homOfLE_comp_of_preimage_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.322128+00:00
-- url     : https://prove2.me/theorems/19221b2e-0985-5d27-b53e-a4620c01b0ed
-- title:
--   Restricting an isomorphism of open subschemes to smaller opens
-- statement:
--   Let $Y$ and $Y'$ be schemes (in a fixed universe), let $V$ be an open of $Y$ and $V'$ an open of $Y'$, and let $\varphi$ be an isomorphism of schemes between the open subscheme $V$ and the open subscheme $V'$. Let $Z$ be an open of $Y$ with $Z \le V$ and $Z'$ an open of $Y'$ with $Z' \le V'$, and assume that $\varphi$ matches $Z$ and $Z'$ in the sense that the preimage under $\varphi$ of the open $\iota_{V'}^{-1}(Z')$ of $V'$ equals the open $\iota_V^{-1}(Z)$ of $V$, where $\iota_V$ and $\iota_{V'}$ denote the canonical open immersions of $V$ into $Y$ and of $V'$ into $Y'$. The conclusion asserts the existence of an isomorphism $\tau$ between the open subscheme $Z$ of $Y$ and the open subscheme $Z'$ of $Y'$ that is compatible with $\varphi$ in both directions: the composite of $\tau$ with the canonical morphism $Z' \to V'$ attached to $Z' \le V'$ equals the composite of the canonical morphism $Z \to V$ attached to $Z \le V$ with $\varphi$, and the composite of $\tau^{-1}$ with $Z \to V$ equals the composite of $Z' \to V'$ with $\varphi^{-1}$.
--
--   This is the elementary statement that an isomorphism of open subschemes restricts to an isomorphism between any pair of smaller opens that it matches, together with the two commuting squares recording the restriction. It is used in the bookkeeping of ordered affine covers and in the obstruction-theoretic treatment of local lifts along small extensions, where transition isomorphisms over intersections must be restricted to finer opens.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_exists_iso_comp_homOfLE_eq_homOfLE_comp_of_preimage_eq.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.Scheme.exists_iso_comp_homOfLE_eq_homOfLE_comp_of_preimage_eq
    {Y Y' : Scheme.{u}} (V : Y.Opens) (V' : Y'.Opens) (φ : (V : Scheme.{u}) ≅ (V' : Scheme.{u}))
    (Z : Y.Opens) (Z' : Y'.Opens) (hZ : Z ≤ V) (hZ' : Z' ≤ V')
    (hφ : φ.hom ⁻¹ᵁ (V'.ι ⁻¹ᵁ Z') = V.ι ⁻¹ᵁ Z) :
    ∃ τ : (Z : Scheme.{u}) ≅ (Z' : Scheme.{u}),
      τ.hom ≫ Y'.homOfLE hZ' = Y.homOfLE hZ ≫ φ.hom ∧
      τ.inv ≫ Y.homOfLE hZ = Y'.homOfLE hZ' ≫ φ.inv := by sorry
