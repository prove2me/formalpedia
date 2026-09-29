-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_isAffineOpen_forall_mem_of_forall_preimage_mem_of_isFinite_of_flat_of_surjective
-- name    : AlgebraicGeometry.exists_isAffineOpen_forall_mem_of_forall_preimage_mem_of_isFinite_of_flat_of_surjective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.552687+00:00
-- url     : https://prove2.me/theorems/b636db1f-0ba4-5a71-9928-a0de42cf79b4
-- title:
--   Affine neighbourhoods descend along finite locally free surjections
-- statement:
--   Let $p \colon X \to Y$ be a morphism of schemes (in a fixed universe) which is finite, flat, locally of finite presentation and surjective. Let $S$ be a finite set of points of the underlying space of $Y$, given as a `Finset Y`, and let $W$ be an open subscheme of $X$ which is affine, i.e. `IsAffineOpen W` holds. Assume that $W$ contains the whole preimage of $S$: for every point $x$ of $X$ with $p$'s underlying continuous map sending $x$ into $S$, one has $x \in W$. Then there exists an open $V$ of $Y$ which is affine open and contains every element of $S$. Note that the conclusion asserts only the existence of an affine open neighbourhood of $S$ in $Y$; it does not record the further properties (such as $p^{-1}(V)$ being an affine open contained in $W$) that the proof in fact produces.
--
--   This is the descent of affine neighbourhoods of finite sets of points along a finite locally free surjective morphism, in the form going back to SGA 3, Exposé V. In this development it serves to produce affine opens on the base, and is cited in the construction of relative group laws on Jacobians via [`GoodReductionJacobian.RelativeGroupLaw.exists_isAffineOpen_forall_mem_of_forall_mul_mem`](thm.html#GoodReductionJacobian.RelativeGroupLaw.exists_isAffineOpen_forall_mem_of_forall_mul_mem).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_exists_isAffineOpen_forall_mem_of_forall_preimage_mem_of_isFinite_of_flat_of_surjective.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.exists_isAffineOpen_forall_mem_of_forall_preimage_mem_of_isFinite_of_flat_of_surjective
    {X Y : Scheme.{u}} (p : X ⟶ Y) [IsFinite p] [Flat p] [LocallyOfFinitePresentation p] [Surjective p]
    (S : Finset Y) (W : X.Opens) (hW : IsAffineOpen W) (hSW : ∀ x : X, p.base x ∈ S → x ∈ W) :
    ∃ V : Y.Opens, IsAffineOpen V ∧ ∀ y ∈ S, y ∈ V := by sorry
