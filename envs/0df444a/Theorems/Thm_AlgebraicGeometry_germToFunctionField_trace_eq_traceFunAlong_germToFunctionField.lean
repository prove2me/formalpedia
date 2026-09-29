-- Prove2me | Theorems.Thm_AlgebraicGeometry_germToFunctionField_trace_eq_traceFunAlong_germToFunctionField
-- name    : AlgebraicGeometry.germToFunctionField_trace_eq_traceFunAlong_germToFunctionField
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.96328+00:00
-- url     : https://prove2.me/theorems/147dabc6-59c9-5f07-a64a-b953413645a4
-- title:
--   Generic germ of a relative trace is the function-field trace
-- statement:
--   Let $K$ be a field, let $X$ and $Y$ be integral schemes over $\operatorname{Spec} K$ via structure morphisms $c_X : X \to \operatorname{Spec} K$ and $c_Y : Y \to \operatorname{Spec} K$, and let $\pi : Y \to X$ be an affine morphism with $\pi$ followed by $c_X$ equal to $c_Y$. Let $U \subseteq X$ be an affine open with $U$ and $\pi^{-1}U$ both nonempty. The function fields $X.\mathrm{functionField}$ and $Y.\mathrm{functionField}$ (the stalks at the generic points) are regarded as $K$-algebras via [`AlgebraicCurve.baseToFunctionField`](def/AlgebraicCurve_CurveModel.html#L18), i.e. via the inverse of the $\Gamma$–$\operatorname{Spec}$ adjunction isomorphism for $K$, the map on global sections induced by the structure morphism, and the germ at the generic point; and $B := \Gamma(Y, \pi^{-1}U)$ is an algebra over $A := \Gamma(X, U)$ via $\pi^{\ast}$ on $U$. Assume $B$ is free and finite as an $A$-module, and let $\varphi : X.\mathrm{functionField} \to Y.\mathrm{functionField}$ be a $K$-algebra homomorphism such that the canonical morphism from the generic stalk of $Y$ followed by $\pi$ equals $\operatorname{Spec}\varphi$ followed by the canonical morphism from the generic stalk of $X$. Then for every $g \in B$ the germ at the generic point of $X$ of $\operatorname{Tr}_{B/A}(g)$ equals $\operatorname{Tr}_{Y.\mathrm{functionField}/X.\mathrm{functionField}}$, taken along $\varphi$ and viewed as a $K$-linear map, of the germ of $g$ at the generic point of $Y$.
--
--   This is the compatibility of the trace form with passage to the generic point: the relative trace of a finite free algebra of sections computes the field trace of function fields. It is used in the construction of trace maps on relative Picard groups, specifically in [`AlgebraicGeometry.RelPicard.IsDeformationClassMap.exists_cechH1ToH1_germ_eq_traceAlong_of_classifies_normModule_pullback_of_field`](thm.html#AlgebraicGeometry.RelPicard.IsDeformationClassMap.exists_cechH1ToH1_germ_eq_traceAlong_of_classifies_normModule_pullback_of_field).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_germToFunctionField_trace_eq_traceFunAlong_germToFunctionField.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_PlacesOf
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_CechH1PushPull

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve

theorem AlgebraicGeometry.germToFunctionField_trace_eq_traceFunAlong_germToFunctionField
    {K : Type u} [Field K] {X Y : Scheme.{u}} (cX : X ⟶ Spec (.of K)) (cY : Y ⟶ Spec (.of K))
    [IsIntegral X] [IsIntegral Y] (π : Y ⟶ X) [IsAffineHom π] (hπ : π ≫ cX = cY)
    (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U] [Nonempty (π ⁻¹ᵁ U : Y.Opens)] :
    letI := (AlgebraicCurve.baseToFunctionField cX).toAlgebra
    letI := (AlgebraicCurve.baseToFunctionField cY).toAlgebra
    letI : Algebra Γ(X, U) Γ(Y, π ⁻¹ᵁ U) := (π.app U).hom.toAlgebra
    ∀ [Module.Free Γ(X, U) Γ(Y, π ⁻¹ᵁ U)] [Module.Finite Γ(X, U) Γ(Y, π ⁻¹ᵁ U)]
      (φ : X.functionField →ₐ[K] Y.functionField)
      (hφπ : Y.fromSpecStalk (genericPoint Y) ≫ π =
        Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ X.fromSpecStalk (genericPoint X))
      (g : Γ(Y, π ⁻¹ᵁ U)),
      (X.germToFunctionField U).hom (Algebra.trace Γ(X, U) Γ(Y, π ⁻¹ᵁ U) g) =
        AlgebraicCurve.traceFunAlong φ ((Y.germToFunctionField (π ⁻¹ᵁ U)).hom g) := by sorry
