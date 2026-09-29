-- Prove2me | Theorems.Thm_AlgebraicCurve_preimage_restrictAlong_placesOf_subset_placesOf_preimage
-- name    : AlgebraicCurve.preimage_restrictAlong_placesOf_subset_placesOf_preimage
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.617196+00:00
-- url     : https://prove2.me/theorems/36e2f216-8555-57f3-ade1-db453056b66a
-- title:
--   Places restricting into Pl_X(U) are centred over π⁻¹U
-- statement:
--   Let $K$ be a field and let $X, Y$ be integral schemes equipped with morphisms $c_X \colon X \to \operatorname{Spec} K$ and $c_Y \colon Y \to \operatorname{Spec} K$, where $c_X$ is separated, $c_Y$ is proper, and both are smooth of relative dimension $1$; the function fields $X.\mathrm{functionField}$ and $Y.\mathrm{functionField}$ are regarded as $K$-algebras via `baseToFunctionField`, the germ at the generic point of the global sections pulled back along the structure morphism. Let $\pi \colon Y \to X$ be a universally closed morphism of schemes, let $\varphi \colon X.\mathrm{functionField} \to Y.\mathrm{functionField}$ be a $K$-algebra homomorphism whose underlying ring homomorphism is integral, and assume that $\varphi$ computes $\pi$ on generic stalks, in the sense that the canonical morphism from the spectrum of the stalk at the generic point of $Y$ followed by $\pi$ equals $\operatorname{Spec}(\varphi)$ followed by the canonical morphism from the spectrum of the stalk at the generic point of $X$. Here a place of $F/K$ is a valuation subring of $F$ containing the image of $K$, different from $F$ itself and a principal ideal ring; $\mathrm{Place.restrictAlong}\ \varphi$ sends a place $w$ of $Y.\mathrm{functionField}$ to the place with valuation subring $\varphi^{-1}(\mathcal{O}_w)$; and for an open $V$ of a scheme $C$ over $K$, $\mathrm{placesOf}$ is the set of places $v$ of $C.\mathrm{functionField}$ for which there is a closed point $x \in V$ with the image of $\mathcal{O}_{C,x}$ in $C.\mathrm{functionField}$ equal to $\mathcal{O}_v$. The assertion is that for every open $U \subseteq X$, every place $w$ of $Y.\mathrm{functionField}$ whose restriction along $\varphi$ lies in $\mathrm{placesOf}\ c_X\ U$ lies in $\mathrm{placesOf}\ c_Y\ (\pi^{-1}U)$.
--
--   This is one of the two inclusions identifying the places of $Y$ centred over an open $U \subseteq X$ with the preimage, under restriction of places along $\varphi$, of the places of $X$ centred in $U$: every place of the proper smooth curve $Y$ whose restriction is centred in $U$ is itself centred in $\pi^{-1}U$. It is used to prove the corresponding equality of sets of places, which links the scheme-theoretic picture of a curve over $K$ with the valuation-theoretic model of its function field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_preimage_restrictAlong_placesOf_subset_placesOf_preimage.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_PlacesOf
import Definitions.Def_AlgebraicCurve_Correspondence

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry AlgebraicCurve

theorem AlgebraicCurve.preimage_restrictAlong_placesOf_subset_placesOf_preimage
    {K : Type u} [Field K] {X Y : Scheme.{u}}
    (cX : X ⟶ Spec (CommRingCat.of K)) (cY : Y ⟶ Spec (CommRingCat.of K))
    [IsIntegral X] [IsIntegral Y] [IsSeparated cX] [SmoothOfRelativeDimension 1 cX]
    [IsProper cY] [SmoothOfRelativeDimension 1 cY]
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
    (Place.restrictAlong φ hφ) ⁻¹' placesOf cX U ⊆ placesOf cY (π ⁻¹ᵁ U) := by sorry
