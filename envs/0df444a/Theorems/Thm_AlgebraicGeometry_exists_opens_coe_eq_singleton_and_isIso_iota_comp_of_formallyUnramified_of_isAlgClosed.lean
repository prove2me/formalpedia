-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_opens_coe_eq_singleton_and_isIso_iota_comp_of_formallyUnramified_of_isAlgClosed
-- name    : AlgebraicGeometry.exists_opens_coe_eq_singleton_and_isIso_iota_comp_of_formallyUnramified_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.552687+00:00
-- url     : https://prove2.me/theorems/d0768010-0d8a-5c51-bd31-8c29af0d147c
-- title:
--   Points of an unramified finite-type scheme over ̄ k are open and rational
-- statement:
--   Let $k$ be an algebraically closed field, $H$ a scheme, and $q : H \to \operatorname{Spec} k$ a morphism of schemes that is locally of finite type and formally unramified (the Mathlib morphism properties `LocallyOfFiniteType` and `FormallyUnramified`); here $\operatorname{Spec} k$ is the spectrum of $k$ viewed as a commutative ring. The assertion is that for every point $x$ of the underlying topological space of $H$ there exists an open subscheme $U$ of $H$ whose underlying set is exactly the singleton $\{x\}$ and such that the composite of the canonical open immersion $U.\iota : U \to H$ with $q$ is an isomorphism of schemes $U \xrightarrow{\ \sim\ } \operatorname{Spec} k$. In other words, each point of $H$ is open in $H$, the reduced-free open subscheme structure it carries as an open subscheme is that of $\operatorname{Spec} k$, and $x$ is a $k$-rational point; no separatedness, quasi-compactness or finiteness hypothesis on $q$ beyond local finite type is imposed.
--
--   This is the standard structure statement for unramified schemes locally of finite type over an algebraically closed field: such a scheme is a disjoint union of copies of $\operatorname{Spec} k$, stated here pointwise. It is used in the proof that a formally unramified morphism all of whose relevant elements are idempotent factors through a spectrum map, part of the scheme-theoretic input to the deformation-theoretic arguments.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_exists_opens_coe_eq_singleton_and_isIso_iota_comp_of_formallyUnramified_of_isAlgClosed.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

universe u

theorem AlgebraicGeometry.exists_opens_coe_eq_singleton_and_isIso_iota_comp_of_formallyUnramified_of_isAlgClosed
    {k : Type u} [Field k] [IsAlgClosed k] {H : Scheme.{u}} (q : H ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType q] [FormallyUnramified q] (x : H) :
    ∃ U : H.Opens, (U : Set H) = {x} ∧ IsIso (U.ι ≫ q) := by sorry
