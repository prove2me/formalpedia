-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_eq_zero_of_forall_app_eq_zero_of_isIntegral
-- name    : AlgebraicGeometry.Scheme.Modules.IsInvertible.eq_zero_of_forall_app_eq_zero_of_isIntegral
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.517283+00:00
-- url     : https://prove2.me/theorems/f26a0f6d-3838-50a1-be9c-5637f2f7cc9c
-- title:
--   Vanishing on a non-empty open forces vanishing (invertible target)
-- statement:
--   Let $X$ be a scheme that is integral, and let $M$, $N$ be sheaves of modules over the structure sheaf of $X$ (objects of `X.Modules`). Assume $N$ satisfies the predicate `Scheme.Modules.IsInvertible`, namely that for every point $x$ of $X$ there is an open subset $U$ of $X$ containing $x$ such that the pullback of $N$ along the inclusion morphism $U.\iota : U \to X$ is isomorphic to the unit module (the structure sheaf viewed as a module over itself) of the scheme $U$. Let $f : M \to N$ be a morphism of modules, let $U$ be an open subset of $X$ whose underlying set is non-empty, and suppose that for every open subset $V$ of $X$ with $V \le U$ the component $f_V$ of $f$ on sections over $V$ is the zero map. The conclusion is that $f$ is the zero morphism $M \to N$. Note that only the target is assumed invertible; no hypothesis is placed on $M$ beyond its being a module over the structure sheaf.
--
--   This is the standard torsion-freeness statement for invertible modules on an integral scheme: a homomorphism into an invertible module is determined by its restriction to any non-empty open subset. It is used here to derive that a composite of morphisms is non-zero ([`AlgebraicGeometry.Scheme.Modules.IsInvertible.comp_ne_zero_of_ne_zero_of_isIntegral`](thm.html#AlgebraicGeometry.Scheme.Modules.IsInvertible.comp_ne_zero_of_ne_zero_of_isIntegral)), in the line-bundle and relative Picard functor material.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_eq_zero_of_forall_app_eq_zero_of_isIntegral.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.IsInvertible.eq_zero_of_forall_app_eq_zero_of_isIntegral
    {X : Scheme.{u}} [IsIntegral X] {M N : X.Modules} (hN : Scheme.Modules.IsInvertible N) (f : M ⟶ N)
    (U : X.Opens) (hU : Nonempty U) (h : ∀ V : X.Opens, V ≤ U → f.app V = 0) : f = 0 := by sorry
