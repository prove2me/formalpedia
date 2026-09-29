-- Prove2me | Theorems.Thm_AlgebraicCurve_placesOf_preimage_subset_preimage_restrictAlong_placesOf
-- name    : AlgebraicCurve.placesOf_preimage_subset_preimage_restrictAlong_placesOf
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.617196+00:00
-- url     : https://prove2.me/theorems/19ac1979-a571-5bd3-8438-54afdbc336fa
-- title:
--   Places centred in π⁻¹U restrict to places centred in U
-- statement:
--   Let $K$ be a field and let $X$, $Y$ be integral schemes equipped with morphisms $c_X \colon X \to \operatorname{Spec} K$ and $c_Y \colon Y \to \operatorname{Spec} K$, so that the function fields $K(X)$, $K(Y)$ (the stalks at the generic points) become $K$-algebras via `baseToFunctionField`, i.e. the germ at the generic point of the global sections map of the structure morphism. Assume $c_X$ is smooth of relative dimension $1$, and let $\pi \colon Y \to X$ be a universally closed morphism. Let $\varphi \colon K(X) \to K(Y)$ be a $K$-algebra homomorphism whose underlying ring homomorphism is integral, and assume that $\varphi$ computes $\pi$ at the generic points: the composite of $Y.\mathrm{fromSpecStalk}$ at the generic point of $Y$ with $\pi$ equals $\operatorname{Spec}\varphi$ followed by $X.\mathrm{fromSpecStalk}$ at the generic point of $X$. Let $U$ be an open subscheme of $X$. Here a place of $F/K$ is a valuation subring of $F$ containing the image of $K$, different from $F$, and a principal ideal ring; $\mathrm{placesOf}\,c\,U$ is the set of places $v$ for which there is a closed point $x \in U$ with $\mathcal{O}_v$ equal to the image of $\mathcal{O}_{C,x} \to K(C)$; and $\mathrm{Place.restrictAlong}\,\varphi\,h_\varphi\,w$ is the place with valuation ring $\varphi^{-1}\mathcal{O}_w$. The conclusion: every place of $K(Y)/K$ centred at a closed point of $\pi^{-1}U$ has its restriction along $\varphi$ centred at a closed point of $U$.
--
--   This is the inclusion half of the compatibility between the open $U \subseteq X$ and its preimage $\pi^{-1}U$ for the place-theoretic description of closed points of a smooth curve: a place of $K(Y)$ centred over $\pi^{-1}U$ restricts to a place of $K(X)$ centred over $U$. It is used to obtain the equality [`AlgebraicCurve.placesOf_preimage_eq_preimage_restrictAlong_placesOf`](thm.html#AlgebraicCurve.placesOf_preimage_eq_preimage_restrictAlong_placesOf), which matches the place sets of an open cover of $X$ with those of its preimage cover.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_placesOf_preimage_subset_preimage_restrictAlong_placesOf.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_PlacesOf
import Definitions.Def_AlgebraicCurve_Correspondence

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry AlgebraicCurve

theorem AlgebraicCurve.placesOf_preimage_subset_preimage_restrictAlong_placesOf
    {K : Type u} [Field K] {X Y : Scheme.{u}}
    (cX : X ⟶ Spec (CommRingCat.of K)) (cY : Y ⟶ Spec (CommRingCat.of K))
    [IsIntegral X] [IsIntegral Y] [SmoothOfRelativeDimension 1 cX]
    (π : Y ⟶ X) [UniversallyClosed π]
    (φ : letI := (baseToFunctionField cX).toAlgebra
      letI := (baseToFunctionField cY).toAlgebra
      X.functionField →ₐ[K] Y.functionField)
    (hφ : letI := (baseToFunctionField cX).toAlgebra
      letI := (baseToFunctionField cY).toAlgebra
      φ.toRingHom.IsIntegral)
    (hφπ : letI := (baseToFunctionField cX).toAlgebra
      letI := (baseToFunctionField cY).toAlgebra
      Y.fromSpecStalk (genericPoint Y) ≫ π =
        Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ X.fromSpecStalk (genericPoint X))
    (U : X.Opens) :
    letI := (baseToFunctionField cX).toAlgebra
    letI := (baseToFunctionField cY).toAlgebra
    placesOf cY (π ⁻¹ᵁ U) ⊆ (Place.restrictAlong φ hφ) ⁻¹' placesOf cX U := by sorry
