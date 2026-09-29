-- Prove2me | Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_exists_isAffineOpen_forall_mem_of_finset
-- name    : AlgebraicCurve.TwoChartIntegralModel.exists_isAffineOpen_forall_mem_of_finset
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.26765+00:00
-- url     : https://prove2.me/theorems/c33fa972-2f07-54ba-aa9e-c6bb8e2549fe
-- title:
--   Finite sets of points of the two-chart integral model lie in an affine open
-- statement:
--   Let $R$ be a commutative ring, let $F$ be a field equipped with an $R$-algebra structure, and let $j$ be a nonzero element of $F$. Write $\mathfrak{X} =$ [`AlgebraicCurve.TwoChartIntegralModel R F j`](def/AlgebraicCurve_TwoChartIntegralModel.html#L236) for the scheme obtained as the pushout, in the category of schemes over the universe $u$, of the two morphisms $\mathrm{Spec}$ of the ring maps underlying `inclFin R F j` and `inclInf R F j`, i.e. of `fFin R F j : XMid R F j ⟶ XFin R F j` and `fInf R F j : XMid R F j ⟶ XInf R F j`; thus $\mathfrak{X}$ is the scheme got by glueing the two charts $X_{\mathrm{fin}}$ and $X_{\mathrm{inf}}$ along $X_{\mathrm{mid}}$. The assertion is that for every finite set $S$ of points of the underlying space of $\mathfrak{X}$ there exists an open subset $W$ of $\mathfrak{X}$ which is an affine open (`IsAffineOpen W`) and contains every $x \in S$.
--
--   This is the standard prime-avoidance statement that on a scheme affine over the projective line any finite set of points is contained in an affine open, specialised to the two-chart integral model built from the $j$-chart and the $1/j$-chart. It is obtained from the general two-chart criterion [`AlgebraicGeometry.exists_isAffineOpen_forall_mem_of_finset_of_twoCharts`](thm.html#AlgebraicGeometry.exists_isAffineOpen_forall_mem_of_finset_of_twoCharts), and is used for the refinements [`AlgebraicCurve.TwoChartIntegralModel.exists_isAffineOpen_le_preimage_forall_mem_of_finset`](thm.html#AlgebraicCurve.TwoChartIntegralModel.exists_isAffineOpen_le_preimage_forall_mem_of_finset) and [`AlgebraicCurve.TwoChartIntegralModel.exists_isAffineOpen_subset_of_finite_of_isClosed_baseChange`](thm.html#AlgebraicCurve.TwoChartIntegralModel.exists_isAffineOpen_subset_of_finite_of_isClosed_baseChange), and further in the modular curve input [`ModularCurve.nonempty_legTwoInputV2`](thm.html#ModularCurve.nonempty_legTwoInputV2).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_TwoChartIntegralModel_exists_isAffineOpen_forall_mem_of_finset.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve AlgebraicCurve.TwoChartIntegralModel

theorem AlgebraicCurve.TwoChartIntegralModel.exists_isAffineOpen_forall_mem_of_finset
    (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]
    (S : Finset ↥(AlgebraicCurve.TwoChartIntegralModel R F j)) :
    ∃ W : (AlgebraicCurve.TwoChartIntegralModel R F j).Opens, IsAffineOpen W ∧ ∀ x ∈ S, x ∈ W := by sorry
