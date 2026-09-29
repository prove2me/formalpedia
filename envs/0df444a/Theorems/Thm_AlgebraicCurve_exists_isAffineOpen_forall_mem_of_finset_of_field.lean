-- Prove2me | Theorems.Thm_AlgebraicCurve_exists_isAffineOpen_forall_mem_of_finset_of_field
-- name    : AlgebraicCurve.exists_isAffineOpen_forall_mem_of_finset_of_field
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.809948+00:00
-- url     : https://prove2.me/theorems/0f05f260-54c4-5451-94dc-973d7174702c
-- title:
--   Finitely many points of a proper smooth curve lie in an affine open
-- statement:
--   Let $K$ be a field, let $C$ be a scheme, and let $c : C \to \operatorname{Spec} K$ be a morphism of schemes, where $\operatorname{Spec} K$ is the spectrum of $K$ viewed as a commutative ring object. Assume that $C$ is an integral scheme, that $c$ is a proper morphism, and that $c$ is smooth of relative dimension $1$. Then for every finite set $F$ of points of the underlying topological space of $C$ there exists an open subscheme $U$ of $C$ (an element of `C.Opens`) such that $U$ is an affine open, i.e. the scheme it carries is affine, and every point $x \in F$ lies in $U$. Note that $F$ is a `Finset` of points of $C$ and the conclusion asserts containment pointwise, with no further condition on $U$ (in particular nothing is said about the complement of $U$, nor is $U$ required to be non-empty beyond containing $F$).
--
--   This is the standard fact that a finite set of points on a proper smooth curve over a field is contained in an affine open subscheme, obtained here with no projectivity hypothesis beyond properness. It is used in the refinement [`AlgebraicCurve.exists_isAffineOpen_forall_mem_and_finite_compl`](thm.html#AlgebraicCurve.exists_isAffineOpen_forall_mem_and_finite_compl), which additionally controls the complement of the affine open, and thereby in the passage from curves to affine models in the arithmetic of elliptic curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_exists_isAffineOpen_forall_mem_of_finset_of_field.lean

import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

theorem AlgebraicCurve.exists_isAffineOpen_forall_mem_of_finset_of_field
    {K : Type u} [Field K] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of K))
    [IsIntegral C] [IsProper c] [SmoothOfRelativeDimension 1 c]
    (F : Finset C) :
    ∃ U : C.Opens, IsAffineOpen U ∧ ∀ x ∈ F, x ∈ U := by sorry
