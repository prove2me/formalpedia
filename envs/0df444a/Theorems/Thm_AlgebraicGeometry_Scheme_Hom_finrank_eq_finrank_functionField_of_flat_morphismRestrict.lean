-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Hom_finrank_eq_finrank_functionField_of_flat_morphismRestrict
-- name    : AlgebraicGeometry.Scheme.Hom.finrank_eq_finrank_functionField_of_flat_morphismRestrict
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.223894+00:00
-- url     : https://prove2.me/theorems/a6d2410e-86ce-57b9-9e86-d2892df9c059
-- title:
--   Rank at a flat point equals the function-field degree
-- statement:
--   Let $X$ and $Y$ be integral schemes and let $\pi \colon X \to Y$ be a finite morphism whose underlying map of points is surjective. Let $\varphi \colon K(Y) \to K(X)$ be a ring homomorphism between the function fields which is compatible with $\pi$ in the sense that the morphism $\operatorname{Spec} \mathcal{O}_{X,\eta_X} \to X$ from the stalk at the generic point of $X$ followed by $\pi$ coincides with $\operatorname{Spec}(\varphi)$ followed by the morphism $\operatorname{Spec} \mathcal{O}_{Y,\eta_Y} \to Y$ from the stalk at the generic point of $Y$. Let $V \subseteq Y$ be an open subscheme such that the restriction $\pi \mid_V$ of $\pi$ over $V$ is flat and locally of finite presentation, and let $y \in V$. Then the rank of the finite morphism $\pi$ at the point $y$ equals $\operatorname{finrank}_{K(Y)} K(X)$, the dimension of $K(X)$ as a vector space over $K(Y)$ via the algebra structure given by $\varphi$.
--
--   This identifies the local rank of a finite morphism of integral schemes, at points where the morphism is flat and locally of finite presentation, with the degree $[K(X):K(Y)]$ of the induced extension of function fields; it is the scheme-theoretic form of the statement that the degree of a finite flat morphism is computed at the generic point. It is used in the construction of degeneracy and Hecke correspondences on integral models of modular curves, where the degree of a finite flat chart map must be read off from the function-field extension.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Hom_finrank_eq_finrank_functionField_of_flat_morphismRestrict.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Hom.finrank_eq_finrank_functionField_of_flat_morphismRestrict
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] (π : X ⟶ Y) [IsFinite π] (hsurj : Function.Surjective π)
    (φ : Y.functionField →+* X.functionField)
    (hφ : X.fromSpecStalk (genericPoint X) ≫ π = Spec.map (CommRingCat.ofHom φ) ≫ Y.fromSpecStalk (genericPoint Y))
    (V : Y.Opens) [Flat (π ∣_ V)] [LocallyOfFinitePresentation (π ∣_ V)] (y : Y) (hy : y ∈ V) :
    π.finrank y = (letI := φ.toAlgebra; Module.finrank Y.functionField X.functionField) := by sorry
