-- Prove2me | Theorems.Thm_AlgebraicGeometry_isClosed_singleton_or_isGenericPoint_and_exists_not_isGenericPoint_of_smoothOfRelativeDimension_one
-- name    : AlgebraicGeometry.isClosed_singleton_or_isGenericPoint_and_exists_not_isGenericPoint_of_smoothOfRelativeDimension_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.96328+00:00
-- url     : https://prove2.me/theorems/2d9da6c5-3552-5e3f-86c0-22422b28fd96
-- title:
--   Smooth proper curve: points are closed or generic, not all generic
-- statement:
--   Let $k$ be an algebraically closed field and let $C$ be a scheme equipped with a morphism $c : C \to \operatorname{Spec} k$ that is proper, smooth of relative dimension $1$, and geometrically integral (the last three being typeclass hypotheses on $c$). The conclusion is the conjunction of two topological assertions about the underlying space of $C$: first, for every point $x$ of $C$, either the singleton $\{x\}$ is closed in $C$ or $x$ is a generic point of the whole space, i.e. the closure of $\{x\}$ is all of $C$; second, there exists a point $x$ of $C$ whose closure is not all of $C$, i.e. which is not a generic point of $C$. Together these say that $C$ is topologically a curve in the crudest sense: its points are either closed or generic, and it is not reduced to a single (generic) point. Note that the algebraic closedness of $k$ is a hypothesis of the statement even though the assertion is purely topological.
--
--   This records the topological one-dimensionality of a smooth proper geometrically integral curve over a field: every point is either closed or the generic point, and closed points exist. It is used in the analysis of the components of special fibres of the modular curve models, in [`ModularCurve.XOneP.exists_comp_eq_fst_comp_heckeDegeneracy_baseChange_of_ne_specialFibre_components_twoChartModel_x1_mul`](thm.html#ModularCurve.XOneP.exists_comp_eq_fst_comp_heckeDegeneracy_baseChange_of_ne_specialFibre_components_twoChartModel_x1_mul) and [`ModularCurve.XOneP.notMem_support_of_closure_mem_irreducibleComponents_of_I_eq_ker_twoChartModel_x1_mul`](thm.html#ModularCurve.XOneP.notMem_support_of_closure_mem_irreducibleComponents_of_I_eq_ker_twoChartModel_x1_mul).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_isClosed_singleton_or_isGenericPoint_and_exists_not_isGenericPoint_of_smoothOfRelativeDimension_one.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.isClosed_singleton_or_isGenericPoint_and_exists_not_isGenericPoint_of_smoothOfRelativeDimension_one
    (k : Type u) [Field k] [IsAlgClosed k] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c] :
    (∀ x : ↥C, IsClosed ({x} : Set ↥C) ∨ IsGenericPoint x (⊤ : Set ↥C)) ∧
    (∃ x : ↥C, ¬ IsGenericPoint x (⊤ : Set ↥C)) := by sorry
