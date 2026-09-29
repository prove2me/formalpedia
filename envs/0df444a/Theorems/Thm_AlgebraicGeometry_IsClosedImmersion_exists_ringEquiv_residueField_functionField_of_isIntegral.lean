-- Prove2me | Theorems.Thm_AlgebraicGeometry_IsClosedImmersion_exists_ringEquiv_residueField_functionField_of_isIntegral
-- name    : AlgebraicGeometry.IsClosedImmersion.exists_ringEquiv_residueField_functionField_of_isIntegral
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.268945+00:00
-- url     : https://prove2.me/theorems/d5e93e45-90b6-55be-8c4d-615bfb15c8e1
-- title:
--   Residue field at the generic point of an integral closed subscheme
-- statement:
--   Let $C$ and $Y$ be schemes in a fixed universe, with $C$ integral, and let $i : C \to Y$ be a closed immersion. Write $\xi$ for the generic point `genericPoint C` of (the underlying space of) $C$, so that the stalk of $C$ at $\xi$ is the function field `C.functionField`, and consider the point $i(\xi)$ of $Y$ obtained by applying the underlying continuous map of $i$. The assertion is that there exists a ring isomorphism $\theta$ from the residue field $\kappa(i(\xi)) =$ `Y.residueField (i.base (genericPoint C))` of $Y$ at that point onto $C$'s function field, which is compatible with the canonical maps out of the stalk in the following sense: for every element $s$ of the stalk $\mathcal{O}_{Y,i(\xi)}$, the image under $\theta$ of the residue of $s$ (the underlying ring map of `Y.residue`) equals the image of $s$ under the underlying ring map of the stalk map $\mathcal{O}_{Y,i(\xi)} \to \mathcal{O}_{C,\xi}$ of $i$ at $\xi$. Thus $\theta$ is uniquely determined: the stalk map of $i$ at the generic point factors through the residue field as an isomorphism onto $K(C)$.
--
--   This is the standard identification $\kappa(i(\xi)) \cong K(C)$ for a closed immersion of an integral scheme, with the factorisation through the residue map recorded so that compatibilities over any base follow from the characterising clause. It is used in the analysis of the models of $X_1(Mp)$, where the function field of a component of a special fibre has to be read off as a residue field of the ambient scheme at the generic point of that component.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_IsClosedImmersion_exists_ringEquiv_residueField_functionField_of_isIntegral.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

universe u

theorem AlgebraicGeometry.IsClosedImmersion.exists_ringEquiv_residueField_functionField_of_isIntegral
    {C Y : Scheme.{u}} [IsIntegral C] (i : C ⟶ Y) [IsClosedImmersion i] :
    ∃ θ : Y.residueField (i.base (genericPoint C)) ≃+* C.functionField,
      ∀ s : Y.presheaf.stalk (i.base (genericPoint C)),
        θ ((Y.residue (i.base (genericPoint C))).hom s) = (i.stalkMap (genericPoint C)).hom s := by sorry
