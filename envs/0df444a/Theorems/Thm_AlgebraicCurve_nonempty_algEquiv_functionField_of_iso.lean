-- Prove2me | Theorems.Thm_AlgebraicCurve_nonempty_algEquiv_functionField_of_iso
-- name    : AlgebraicCurve.nonempty_algEquiv_functionField_of_iso
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.617196+00:00
-- url     : https://prove2.me/theorems/4d5478a1-53df-527d-9d8b-afca4f8b9fa5
-- title:
--   Function fields are K-algebra isomorphic under isomorphism over K
-- statement:
--   Let $K$ be a field and let $X$, $Y$ be integral schemes (all in a single universe), equipped with morphisms $c_X \colon X \to \operatorname{Spec} K$ and $c_Y \colon Y \to \operatorname{Spec} K$, where $\operatorname{Spec} K$ is the spectrum of $K$ viewed as a commutative ring. Suppose given an isomorphism $e \colon X \cong Y$ of schemes compatible with the two structure morphisms, in the sense that $e$ followed by $c_Y$ equals $c_X$. Each of $X$ and $Y$ carries its function field, the stalk of the structure sheaf at the generic point of the underlying space, and each is made into a $K$-algebra by the ring homomorphism `baseToFunctionField` attached to the corresponding structure morphism: the composite of the inverse of the canonical isomorphism $K \cong \Gamma(\operatorname{Spec} K, \mathcal{O})$, the map induced by the structure morphism on global sections, and the germ map from global sections to the stalk at the generic point. With these two $K$-algebra structures, the conclusion is that the type of $K$-algebra equivalences from the function field of $X$ to that of $Y$ is nonempty; no particular isomorphism is named.
--
--   This is the elementary functoriality statement that the function field of an integral scheme over $K$, with its $K$-algebra structure coming from the structure morphism, is an invariant of the scheme up to isomorphism over $K$. It is used in the relative Picard and Riemann–Roch parts of the development, where invariants of a curve defined through its function field (such as the genus) must be transported along isomorphisms of fibres.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_nonempty_algEquiv_functionField_of_iso.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_CurveModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry AlgebraicCurve

theorem AlgebraicCurve.nonempty_algEquiv_functionField_of_iso
    {K : Type u} [Field K] {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (cX : X ⟶ Spec (CommRingCat.of K)) (cY : Y ⟶ Spec (CommRingCat.of K))
    (e : X ≅ Y) (he : e.hom ≫ cY = cX) :
    letI := (baseToFunctionField cX).toAlgebra
    letI := (baseToFunctionField cY).toAlgebra
    Nonempty (X.functionField ≃ₐ[K] Y.functionField) := by sorry
