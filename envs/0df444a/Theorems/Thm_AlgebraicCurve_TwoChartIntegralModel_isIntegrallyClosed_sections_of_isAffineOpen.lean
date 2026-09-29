-- Prove2me | Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_isIntegrallyClosed_sections_of_isAffineOpen
-- name    : AlgebraicCurve.TwoChartIntegralModel.isIntegrallyClosed_sections_of_isAffineOpen
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.26765+00:00
-- url     : https://prove2.me/theorems/033f9016-1d29-5aa1-a40d-d22a45033031
-- title:
--   Sections over affine opens of the two-chart integral model are integrally closed
-- statement:
--   Let $R$ be a commutative ring, $F$ a field equipped with an $R$-algebra structure, and $j \in F$ a nonzero element. Write $\mathcal{X} =$ [`AlgebraicCurve.TwoChartIntegralModel R F j`](def/AlgebraicCurve_TwoChartIntegralModel.html#L236) for the scheme obtained as the pushout, in the category of schemes, of the two morphisms `fFin R F j` and `fInf R F j`, i.e. of $\operatorname{Spec}$ applied to the two algebra inclusions `inclFin R F j` and `inclInf R F j` of the middle chart's coordinate ring into those of the finite and infinite charts; so $\mathcal{X}$ is the scheme glued from the two affine charts along the middle one. The assertion is: for every open subset $U$ of $\mathcal{X}$ which is an affine open (hypothesis `hU : IsAffineOpen U`), the commutative ring of sections $\Gamma(\mathcal{X}, U)$ is integrally closed in the sense of Mathlib's `IsIntegrallyClosed`, namely every element of its fraction ring that is integral over it lies in the image of the structure map. No nonemptiness is required of $U$: the case $U = \bot$, where the ring of sections is the zero ring, is part of the statement.
--
--   This is normality of the two-chart integral model, recorded in the affine-local form in which it is consumed: a statement about $\Gamma(\mathcal{X}, U)$ for affine opens $U$ rather than about the scheme $\mathcal{X}$ itself. It is used for the corresponding normality statement for the Igusa scheme and in the properties of the two-chart models attached to $X_1(p)$ and to Hecke correspondences on them.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_TwoChartIntegralModel_isIntegrallyClosed_sections_of_isAffineOpen.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicCurve.TwoChartIntegralModel.isIntegrallyClosed_sections_of_isAffineOpen
    (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]
    (U : (AlgebraicCurve.TwoChartIntegralModel R F j).Opens) (hU : IsAffineOpen U) :
    IsIntegrallyClosed ↑Γ(AlgebraicCurve.TwoChartIntegralModel R F j, U) := by sorry
