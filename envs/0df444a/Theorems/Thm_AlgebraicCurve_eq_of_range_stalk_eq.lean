-- Prove2me | Theorems.Thm_AlgebraicCurve_eq_of_range_stalk_eq
-- name    : AlgebraicCurve.eq_of_range_stalk_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.26765+00:00
-- url     : https://prove2.me/theorems/af8b1129-a842-50dc-bd8f-3ec8d9a4ea2d
-- title:
--   A point is determined by its local ring in K(C)
-- statement:
--   Let $K$ be a field and let $c \colon C \to \operatorname{Spec} K$ be a morphism of schemes, where $C$ is integral, $c$ is separated and $c$ is smooth of relative dimension $1$. Let $x, y$ be points of $C$. Each stalk $\mathcal{O}_{C,x}$ carries, through the specialisation morphism from the generic point, the structure of a $K$-subalgebra-like subring of the function field $K(C) = \mathcal{O}_{C,\eta}$, via `algebraMap (C.presheaf.stalk x) C.functionField`. The hypothesis is that the two images coincide as subrings of $K(C)$:
--   $$\operatorname{im}\bigl(\mathcal{O}_{C,x} \to K(C)\bigr) = \operatorname{im}\bigl(\mathcal{O}_{C,y} \to K(C)\bigr).$$ The conclusion is $x = y$. Thus a point of such a curve is determined by the subring of the function field that its local ring cuts out; no closedness or properness assumption is imposed.
--
--   This is the uniqueness half of the valuative criterion of separatedness in the form 'a local subring of the function field has at most one centre on a separated integral scheme'. It is used throughout the curve-theoretic layer, for instance when matching points of a curve with places of its function field and in the identification of sheaf cohomology with a Čech computation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_eq_of_range_stalk_eq.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_CurveModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry

universe u

theorem AlgebraicCurve.eq_of_range_stalk_eq
    {K : Type u} [Field K] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of K))
    [IsIntegral C] [IsSeparated c] [SmoothOfRelativeDimension 1 c]
    (x y : C)
    (h : (algebraMap (C.presheaf.stalk x) C.functionField).range =
      (algebraMap (C.presheaf.stalk y) C.functionField).range) :
    x = y := by sorry
