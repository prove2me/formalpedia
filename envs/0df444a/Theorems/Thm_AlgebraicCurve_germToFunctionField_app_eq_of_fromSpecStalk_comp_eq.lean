-- Prove2me | Theorems.Thm_AlgebraicCurve_germToFunctionField_app_eq_of_fromSpecStalk_comp_eq
-- name    : AlgebraicCurve.germToFunctionField_app_eq_of_fromSpecStalk_comp_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.617196+00:00
-- url     : https://prove2.me/theorems/6eecb162-1c2a-58c9-954e-1ea1d708b84e
-- title:
--   Generic germ commutes with pull-back of sections
-- statement:
--   Let $X$ and $Y$ be schemes (in a fixed universe) that are integral, let $\pi : Y \to X$ be a morphism of schemes, and let $\varphi : K(X) \to K(Y)$ be a ring homomorphism between their function fields, i.e.\ between the stalks at the respective generic points, as given by `Scheme.functionField`. Assume the compatibility $$\bigl(\operatorname{Spec} K(Y) \to Y \xrightarrow{\pi} X\bigr) = \bigl(\operatorname{Spec} K(Y) \xrightarrow{\operatorname{Spec}\varphi} \operatorname{Spec} K(X) \to X\bigr),$$ where the unlabelled arrows are the canonical morphisms `fromSpecStalk` from the spectrum of the stalk at the generic point. Let $U$ be an open subscheme of $X$, assume that both $U$ and its preimage $\pi^{-1}U$ are nonempty as schemes, and let $s \in \Gamma(X, U)$ be a section of the structure sheaf on $U$. Then the germ at the generic point of $Y$ of the pulled-back section $\pi^\sharp(s) \in \Gamma(Y, \pi^{-1}U)$ equals $\varphi$ applied to the germ of $s$ at the generic point of $X$; that is, $(\text{germ to } K(Y))(\pi^\sharp s) = \varphi\bigl((\text{germ to } K(X))(s)\bigr)$ in $K(Y)$.
--
--   This is the naturality of passage to rational functions: restricting regular functions to the generic point commutes with pull-back along a morphism of integral schemes whose generic fibre is the given inclusion of function fields. It is the bookkeeping used to compare sections and Čech cocycles for $\mathcal{O}$ on $X$ and on $Y$ inside the function fields, and is invoked when degeneracy morphisms of curves are matched with embeddings of function fields, in the computation of traces and of ranks of function-field extensions along flat morphisms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_germToFunctionField_app_eq_of_fromSpecStalk_comp_eq.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicCurve.germToFunctionField_app_eq_of_fromSpecStalk_comp_eq
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] (π : Y ⟶ X)
    (φ : X.functionField →+* Y.functionField)
    (hφπ : Y.fromSpecStalk (genericPoint Y) ≫ π =
      Spec.map (CommRingCat.ofHom φ) ≫ X.fromSpecStalk (genericPoint X))
    (U : X.Opens) [Nonempty (U : Scheme.{u})] [Nonempty ((π ⁻¹ᵁ U : Y.Opens) : Scheme.{u})] (s : Γ(X, U)) :
    (Y.germToFunctionField (π ⁻¹ᵁ U)).hom (π.app U s) = φ ((X.germToFunctionField U).hom s) := by sorry
