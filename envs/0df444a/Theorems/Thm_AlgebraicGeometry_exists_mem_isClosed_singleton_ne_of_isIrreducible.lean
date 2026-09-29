-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_mem_isClosed_singleton_ne_of_isIrreducible
-- name    : AlgebraicGeometry.exists_mem_isClosed_singleton_ne_of_isIrreducible
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.552687+00:00
-- url     : https://prove2.me/theorems/095ffc90-a0bf-5754-a54b-2b79c09a4390
-- title:
--   A non-singleton closed subset has a closed point other than x
-- statement:
--   Let $k$ be a field and let $t\colon X\to\operatorname{Spec}k$ be a morphism from a scheme $X$ to the spectrum of $k$ which is locally of finite type. Let $Z\subseteq X$ be a subset of the underlying topological space of $X$ which is closed and irreducible (irreducible in Mathlib's sense: non-empty and not contained in the union of two closed sets unless contained in one of them), let $x$ be a point of $X$ lying in $Z$ whose singleton $\{x\}$ is closed in $X$, and assume $Z\neq\{x\}$ as subsets of $X$. Then there exists a point $x'\in Z$ such that $\{x'\}$ is closed in $X$ and $x'\neq x$.
--
--   This is the standard consequence of the fact that a scheme locally of finite type over a field is a Jacobson space: the closed points are dense in every closed subset, so a closed subset containing a closed point $x$ and no other closed point must be $\{x\}$. It is used in the finiteness criterion [`AlgebraicGeometry.Scheme.Modules.ProjPresentation.isFinite_toProj_of_forall_pullbackSection_eq_zero_iff`](thm.html#AlgebraicGeometry.Scheme.Modules.ProjPresentation.isFinite_toProj_of_forall_pullbackSection_eq_zero_iff), where a positive-dimensional closed irreducible subset has to be separated from a chosen closed point.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_exists_mem_isClosed_singleton_ne_of_isIrreducible.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.exists_mem_isClosed_singleton_ne_of_isIrreducible
    (k : Type u) [Field k] {X : Scheme.{u}} (t : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType t]
    (Z : Set X) (hZ : IsClosed Z) (hZ' : IsIrreducible Z)
    (x : X) (hxZ : x ∈ Z) (hx : IsClosed ({x} : Set X)) (hne : Z ≠ {x}) :
    ∃ x' ∈ Z, IsClosed ({x'} : Set X) ∧ x' ≠ x := by sorry
