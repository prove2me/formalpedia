-- Prove2me | Theorems.Thm_AlgebraicGeometry_smoothOfRelativeDimension_of_forall_isClosed_isRegularLocalRing_stalk
-- name    : AlgebraicGeometry.smoothOfRelativeDimension_of_forall_isClosed_isRegularLocalRing_stalk
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.489634+00:00
-- url     : https://prove2.me/theorems/f604b000-eb1c-5e0f-a5bf-010aee817e7c
-- title:
--   Regular local rings at closed points give smoothness of relative dimension n
-- statement:
--   Let $k$ be an algebraically closed field, $Y$ a scheme, and $g : Y \to \operatorname{Spec} k$ a morphism of schemes that is locally of finite type; let $n$ be a natural number. Assume that for every point $y$ of $Y$ such that the singleton $\{y\}$ is closed in the underlying space of $Y$, the stalk $\mathcal{O}_{Y,y}$ of the structure presheaf of $Y$ at $y$ is a regular local ring and its Krull dimension, as an element of the extended naturals, equals $n$. The conclusion is that $g$ has the morphism property `SmoothOfRelativeDimension n`, i.e. $g$ is smooth of relative dimension $n$. Note that regularity and the dimension condition are imposed only at the closed points of $Y$, not at all points, and that the dimension $n$ is the same natural number at every closed point.
--
--   This is the standard criterion identifying smoothness of relative dimension $n$ over an algebraically closed field with regularity of the local rings at closed points together with a constant dimension, in the form of EGA IV §17. It serves as the geometric input for recognising relative curves: it is used to prove the characterisation of smoothness of relative dimension one by the condition that the completed stalks at closed points are power series rings in one variable.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_smoothOfRelativeDimension_of_forall_isClosed_isRegularLocalRing_stalk.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry IsLocalRing

theorem AlgebraicGeometry.smoothOfRelativeDimension_of_forall_isClosed_isRegularLocalRing_stalk
    (k : Type u) [Field k] [IsAlgClosed k] {Y : Scheme.{u}} (g : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType g] (n : ℕ)
    (h : ∀ y : ↥Y, IsClosed ({y} : Set ↥Y) →
      IsRegularLocalRing (Y.presheaf.stalk y) ∧ ringKrullDim (Y.presheaf.stalk y) = (n : ℕ∞)) :
    SmoothOfRelativeDimension n g := by sorry
