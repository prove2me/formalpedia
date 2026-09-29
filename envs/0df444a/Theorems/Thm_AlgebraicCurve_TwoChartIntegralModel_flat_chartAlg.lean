-- Prove2me | Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_flat_chartAlg
-- name    : AlgebraicCurve.TwoChartIntegralModel.flat_chartAlg
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.26765+00:00
-- url     : https://prove2.me/theorems/15ac06be-e0c3-573c-89fb-e6637d908c38
-- title:
--   Flatness of the chart algebra over a Bézout domain
-- statement:
--   Let $R$ be a commutative ring that is a domain and is Bézout (every finitely generated ideal is principal), let $F$ be a field carrying an $R$-algebra structure, and assume the structure map $R \to F$ is injective. For an arbitrary subset $S \subseteq F$, let [`AlgebraicCurve.TwoChartIntegralModel.chartAlg R F S`](def/AlgebraicCurve_TwoChartIntegralModel.html#L26) be the $R$-subalgebra of $F$ whose underlying set consists of those $x \in F$ that are integral over the $R$-subalgebra $R[S] =$ `Algebra.adjoin R S` of $F$ (a subalgebra because integral elements are closed under sums and products and contain the image of $R$). The assertion is that this subalgebra, viewed as an $R$-module, is flat. Note that $R$ and $F$ are taken in the same universe, and that no hypothesis relates $S$ to any further structure: the statement is purely about the integral closure of $R[S]$ in $F$.
--
--   This is the flatness input for the affine charts of the two-chart integral models of modular curves: for $R$ a Bézout domain such as $\mathbb{Z}_{(p)}$ and $S = \{j\}$ or $S = \{1/j\}$ inside a field $F$, the ring of elements integral over $R[S]$ is $R$-flat. It is invoked in the analysis of the chart algebras at full level, for instance in the identifications of base changes of `chartAlg` after adjoining roots of unity and in the study of maximal ideals of those algebras.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_TwoChartIntegralModel_flat_chartAlg.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem AlgebraicCurve.TwoChartIntegralModel.flat_chartAlg
    {R F : Type u} [CommRing R] [IsDomain R] [IsBezout R] [Field F] [Algebra R F]
    (hRF : Function.Injective (algebraMap R F)) (S : Set F) :
    Module.Flat R ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlg R F S) := by sorry
