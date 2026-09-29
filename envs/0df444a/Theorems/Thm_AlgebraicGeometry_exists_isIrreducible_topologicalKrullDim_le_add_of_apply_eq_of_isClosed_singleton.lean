-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_isIrreducible_topologicalKrullDim_le_add_of_apply_eq_of_isClosed_singleton
-- name    : AlgebraicGeometry.exists_isIrreducible_topologicalKrullDim_le_add_of_apply_eq_of_isClosed_singleton
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.552687+00:00
-- url     : https://prove2.me/theorems/ba0827ea-2409-5816-95e0-e1c9de929d68
-- title:
--   Fibre dimension lower bound at a closed point
-- statement:
--   Let $k$ be a field and let $X$, $Y$ be schemes. Let $fX \colon X \to \operatorname{Spec} k$ be a morphism that is locally of finite type, with $X$ irreducible as a topological space, and let $fY \colon Y \to \operatorname{Spec} k$ be a morphism that is locally of finite type. Let $o \colon X \to Y$ be a morphism of schemes compatible with the structure morphisms, in the sense that $o$ followed by $fY$ equals $fX$. Let $y$ be a point of the underlying space of $Y$ such that $\{y\}$ is closed, and let $x$ be a point of the underlying space of $X$ with $o(x) = y$. Then there exists a subset $Z$ of the underlying space of $X$ such that $x \in Z$, such that $Z$ is contained in the set-theoretic fibre $o^{-1}(\{y\})$, such that $Z$ is irreducible and closed, and such that, with all dimensions taken as topological Krull dimensions in $\mathbb{N}_\infty$ adjoined a bottom element (the space $X$, the subspace $Z$, and the closure of the range of $o$ in $Y$, each with its subspace topology), $$\dim X \le \dim Z + \dim \overline{o(X)}.$$
--
--   This is the lower semicontinuity half of the theorem on the dimension of the fibres of a morphism of algebraic schemes over a field, in the form applicable at a closed point of the target: some irreducible closed subset of the fibre through the given point has dimension at least $\dim X - \dim\overline{o(X)}$. It is used in the study of partial actions on good-reduction Jacobians, to produce a closed immersion whose range is a proper subset.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_exists_isIrreducible_topologicalKrullDim_le_add_of_apply_eq_of_isClosed_singleton.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

universe u

theorem AlgebraicGeometry.exists_isIrreducible_topologicalKrullDim_le_add_of_apply_eq_of_isClosed_singleton
    {k : Type u} [Field k] {X Y : Scheme.{u}}
    (fX : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType fX] [IrreducibleSpace ↥X]
    (fY : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType fY]
    (o : X ⟶ Y) (ho : o ≫ fY = fX) {y : ↥Y} (hy : IsClosed ({y} : Set ↥Y))
    {x : ↥X} (hx : o x = y) :
    ∃ Z : Set ↥X, x ∈ Z ∧ Z ⊆ o ⁻¹' {y} ∧ IsIrreducible Z ∧ IsClosed Z ∧
      topologicalKrullDim ↥X ≤
        topologicalKrullDim ↥Z + topologicalKrullDim ↥(closure (Set.range o)) := by sorry
