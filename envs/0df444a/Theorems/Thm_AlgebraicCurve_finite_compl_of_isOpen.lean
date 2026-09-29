-- Prove2me | Theorems.Thm_AlgebraicCurve_finite_compl_of_isOpen
-- name    : AlgebraicCurve.finite_compl_of_isOpen
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.809948+00:00
-- url     : https://prove2.me/theorems/0cbef238-efa3-535b-83ab-9cb32f9456bf
-- title:
--   Nonempty opens on a smooth curve have finite complement
-- statement:
--   Let $K$ be a field and let $C$ be a scheme equipped with a morphism $c \colon C \to \operatorname{Spec} K$ (to the spectrum of $K$ viewed as a commutative ring object). Assume $C$ is an integral scheme, that $c$ is smooth of relative dimension $1$, and that $c$ is quasi-compact. Let $U$ be an open subscheme of $C$ whose underlying set is nonempty. The conclusion is that the complement of $U$ in the underlying topological space of $C$ is a finite set. Thus on such a curve every nonempty open subset omits only finitely many points; equivalently, the closed subsets of $C$ other than $C$ itself are finite. No separatedness or properness assumption is imposed, and the statement is about the underlying point set only, with no scheme structure or degree information attached to the complement.
--
--   This is the basic topological finiteness property of a smooth curve over a field: its proper closed subsets are finite sets of closed points. It underlies the construction of affine opens with prescribed finite behaviour on such curves, and is used in the treatment of orders of vanishing at places of a curve model.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_finite_compl_of_isOpen.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicCurve.finite_compl_of_isOpen
    {K : Type u} [Field K] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of K))
    [IsIntegral C] [SmoothOfRelativeDimension 1 c] [QuasiCompact c]
    (U : C.Opens) (hU : (U : Set C).Nonempty) :
    ((U : Set C)ᶜ).Finite := by sorry
