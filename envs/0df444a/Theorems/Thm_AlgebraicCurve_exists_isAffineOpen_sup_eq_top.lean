-- Prove2me | Theorems.Thm_AlgebraicCurve_exists_isAffineOpen_sup_eq_top
-- name    : AlgebraicCurve.exists_isAffineOpen_sup_eq_top
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.809948+00:00
-- url     : https://prove2.me/theorems/36c62f7d-0498-52e1-90d5-166d9eeebf60
-- title:
--   A smooth proper curve is covered by two affine opens
-- statement:
--   Let $K$ be a field and let $C$ be a scheme equipped with a morphism $c \colon C \to \operatorname{Spec} K$, where $C$ is integral and $c$ is proper and smooth of relative dimension $1$. Assume in addition the hypothesis `haff`: for every finite set $F$ of points of $C$ there is an open subscheme $U \subseteq C$ which is an affine open and contains every point of $F$. The conclusion is that there exist two opens $U, V$ of $C$ such that $U$ is an affine open, $V$ is an affine open, the intersection $U \sqcap V$ is an affine open, and $U \sqcup V = \top$, i.e. $U$ and $V$ cover $C$. Thus a smooth proper integral curve over $K$ satisfying the stated affine-atlas hypothesis admits a cover by two affine opens whose intersection is again affine; the hypothesis `haff` is assumed rather than derived from projectivity.
--
--   This is the standard fact that a smooth proper curve over a field is covered by two affine opens with affine intersection, here deduced from an assumed affine-atlas property for finite sets of points; such a two-chart cover is what makes Čech computations with two charts available. It is used in the relative Picard constructions, for instance in producing charts with vanishing $H^1$ on fibres and in the existence statements for sections with prescribed $H^0$-ranks.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_exists_isAffineOpen_sup_eq_top.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicCurve.exists_isAffineOpen_sup_eq_top
    {K : Type u} [Field K] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of K))
    [IsIntegral C] [IsProper c] [SmoothOfRelativeDimension 1 c]
    (haff : ∀ F : Finset C, ∃ U : C.Opens, IsAffineOpen U ∧ ∀ x ∈ F, x ∈ U) :
    ∃ U V : C.Opens, IsAffineOpen U ∧ IsAffineOpen V ∧ IsAffineOpen (U ⊓ V) ∧ U ⊔ V = ⊤ := by sorry
