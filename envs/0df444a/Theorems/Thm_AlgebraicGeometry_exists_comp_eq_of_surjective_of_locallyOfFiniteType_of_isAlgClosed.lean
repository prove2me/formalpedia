-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_comp_eq_of_surjective_of_locallyOfFiniteType_of_isAlgClosed
-- name    : AlgebraicGeometry.exists_comp_eq_of_surjective_of_locallyOfFiniteType_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.195734+00:00
-- url     : https://prove2.me/theorems/d70738cf-391a-57f3-b30d-1dcffeb0bdc2
-- title:
--   Lifting K-points along surjective morphisms locally of finite type
-- statement:
--   Let $K$ be an algebraically closed field, and let $f \colon X \to Y$ be a morphism of schemes (all in a fixed universe) which is locally of finite type and surjective. Then for every morphism $y \colon \operatorname{Spec} K \to Y$ there exists a morphism $x \colon \operatorname{Spec} K \to X$ with $x$ followed by $f$ equal to $y$; that is, every $K$-valued point of $Y$ lifts to a $K$-valued point of $X$ along $f$.
--
--   This is the standard fact that a surjective morphism locally of finite type is surjective on points with values in an algebraically closed field, a consequence of the Nullstellensatz in its Jacobson-scheme form. It is used in the project to pass between surjectivity of a morphism of schemes and surjectivity on $K$-points, for instance in the Cerednik–Drinfeld material and in the criterion for lifting points of $\operatorname{Spec}$ of a field along morphisms locally of finite type.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_exists_comp_eq_of_surjective_of_locallyOfFiniteType_of_isAlgClosed.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.exists_comp_eq_of_surjective_of_locallyOfFiniteType_of_isAlgClosed
    {K : Type u} [Field K] [IsAlgClosed K] {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f] [Surjective f]
    (y : Spec (.of K) ⟶ Y) :
    ∃ x : Spec (.of K) ⟶ X, x ≫ f = y := by sorry
