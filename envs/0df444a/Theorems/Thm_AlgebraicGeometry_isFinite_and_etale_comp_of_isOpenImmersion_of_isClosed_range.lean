-- Prove2me | Theorems.Thm_AlgebraicGeometry_isFinite_and_etale_comp_of_isOpenImmersion_of_isClosed_range
-- name    : AlgebraicGeometry.isFinite_and_etale_comp_of_isOpenImmersion_of_isClosed_range
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.96328+00:00
-- url     : https://prove2.me/theorems/d6adf80b-6e72-5c40-b760-9a79ea461aa7
-- title:
--   Clopen piece of a finite étale cover is finite étale
-- statement:
--   Let $V$, $U$, $X$ be schemes (in a fixed universe), let $i \colon V \to U$ be a morphism of schemes that is an open immersion, and assume that the range of the underlying continuous map of $i$ is a closed subset of the topological space of $U$; thus $i$ exhibits $V$ as an open subscheme whose image is also closed, i.e. a clopen piece of $U$. Let $\pi \colon U \to X$ be a morphism that is finite and étale in the sense of Mathlib's `IsFinite` and `AlgebraicGeometry.Etale` classes. The conclusion is the conjunction that the composite $i$ followed by $\pi$, namely $\pi \circ i \colon V \to X$, is again finite and is again étale. The two properties are asserted as a pair of propositions rather than registered as instances.
--
--   This is the standard fact that an open and closed subscheme of a finite étale cover is itself finite étale over the base. It is used in the Čerednik–Drinfel'd part of the development, where a clopen subset of a finite étale cover is singled out (for instance via the bijection between connected components of a scheme over a local ring and those of its closed fibre) and one needs to return to the finite étale setting.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_isFinite_and_etale_comp_of_isOpenImmersion_of_isClosed_range.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.isFinite_and_etale_comp_of_isOpenImmersion_of_isClosed_range
    {V U X : Scheme.{u}} (i : V ⟶ U) [IsOpenImmersion i] (hi : IsClosed (Set.range i.base))
    (π : U ⟶ X) [IsFinite π] [AlgebraicGeometry.Etale π] :
    IsFinite (i ≫ π) ∧ AlgebraicGeometry.Etale (i ≫ π) := by sorry
