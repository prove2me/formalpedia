-- Prove2me | Theorems.Thm_AlgebraicCurve_placesOf_preimage_eq_preimage_restrictAlong_placesOf
-- name    : AlgebraicCurve.placesOf_preimage_eq_preimage_restrictAlong_placesOf
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.617196+00:00
-- url     : https://prove2.me/theorems/05f2a466-e316-5f02-aed6-baf546fda25c
-- title:
--   Places centred in a preimage open set
-- statement:
--   Let $K$ be a field and let $cX \colon X \to \operatorname{Spec} K$, $cY \colon Y \to \operatorname{Spec} K$ be morphisms of schemes with $X$ and $Y$ integral; assume $cX$ is separated and smooth of relative dimension $1$, and $cY$ is proper and smooth of relative dimension $1$. The function fields $X.\mathrm{functionField}$ and $Y.\mathrm{functionField}$ (the stalks at the generic points) are regarded as $K$-algebras through `baseToFunctionField`, i.e. through $K \xrightarrow{\sim} \Gamma(\operatorname{Spec} K,\mathcal O) \to \Gamma(X,\mathcal O_X) \to \mathcal O_{X,\eta_X}$ and likewise for $Y$. Let $\pi \colon Y \to X$ be universally closed, let $\varphi \colon K(X) \to K(Y)$ be a $K$-algebra homomorphism whose underlying ring map is integral, and assume $\varphi$ induces $\pi$ on generic stalks: the composite $\operatorname{Spec} K(Y) \to Y \xrightarrow{\pi} X$ equals $\operatorname{Spec} K(Y) \xrightarrow{\operatorname{Spec}\varphi} \operatorname{Spec} K(X) \to X$. Let $U \subseteq X$ be open. Here a place of $F/K$ is a valuation subring of $F$ containing the image of $K$, distinct from $F$ itself, and a principal ideal ring; $\mathrm{placesOf}$ of an open set consists of those places whose valuation subring is the image of $\mathcal O_{\cdot,x} \to F$ for some closed point $x$ of that open set; and $\mathrm{Place.restrictAlong}\ \varphi$ sends a place $w$ of $K(Y)/K$ to the place with valuation subring $\varphi^{-1}(\mathcal O_w)$. The conclusion is the equality of sets: the places of $K(Y)/K$ centred at a closed point of $\pi^{-1}(U)$ are exactly those $w$ whose restriction along $\varphi$ is centred at a closed point of $U$.
--
--   This is the compatibility of centres of places with the morphism $\pi$: for smooth curves, closed points correspond to discrete valuation rings of the function field, and taking preimages of opens corresponds to restricting places along the induced extension of function fields. It is used when identifying the index sets of the function-field Čech complexes attached to an affine cover of $X$ and its preimage cover on $Y$, in the construction of pullback and trace maps on the relevant first Čech cohomology groups.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_placesOf_preimage_eq_preimage_restrictAlong_placesOf.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_PlacesOf
import Definitions.Def_AlgebraicCurve_Correspondence

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry AlgebraicCurve

theorem AlgebraicCurve.placesOf_preimage_eq_preimage_restrictAlong_placesOf
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
    placesOf cY (π ⁻¹ᵁ U) = (Place.restrictAlong φ hφ) ⁻¹' placesOf cX U := by sorry
