-- Prove2me | Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_ringKrullDim_stalk_le_ringKrullDim_add_one
-- name    : AlgebraicCurve.TwoChartIntegralModel.ringKrullDim_stalk_le_ringKrullDim_add_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.26765+00:00
-- url     : https://prove2.me/theorems/0236bd8a-1e14-556e-a5d3-b6c52cf51783
-- title:
--   Stalk dimension bound for the two-chart integral model
-- statement:
--   Let $R$ be a commutative Noetherian ring and $F$ a field equipped with an $R$-algebra structure, and let $j \in F$ be non-zero. Let $X =$ [`AlgebraicCurve.TwoChartIntegralModel R F j`](def/AlgebraicCurve_TwoChartIntegralModel.html#L236) be the scheme obtained as the pushout, in the category of schemes, of the two morphisms $\mathrm{Spec}$ applied to the algebra inclusions `inclFin` and `inclInf`, that is, of `fFin : XMid R F j ⟶ XFin R F j` and `fInf : XMid R F j ⟶ XInf R F j`: the two affine charts $\mathrm{XFin}$ and $\mathrm{XInf}$ glued along the common chart $\mathrm{XMid}$. Then for every point $z$ of the underlying topological space of $X$, the Krull dimension of the stalk $\mathcal{O}_{X,z}$ of the structure presheaf of $X$ at $z$ satisfies $$\dim \mathcal{O}_{X,z} \le \dim R + 1,$$ the inequality being one of extended dimensions (`ringKrullDim` takes values in $\mathbb{N}\infty$ adjoined with a bottom element, so that the empty ring is allowed on either side).
--
--   This is the expected dimension bound for an arithmetic surface built by gluing two affine charts over a Noetherian base: over a Dedekind base or a discrete valuation ring it gives $\dim \mathcal{O}_{X,z} \le 2$. It is used in the study of the integral models of the modular curves occurring in the argument, for instance in localising points of the two-chart model of $X_1(N)$-type curves and in establishing properties of stalks at points of the special fibre.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_TwoChartIntegralModel_ringKrullDim_stalk_le_ringKrullDim_add_one.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicCurve.TwoChartIntegralModel.ringKrullDim_stalk_le_ringKrullDim_add_one
    (R : Type u) [CommRing R] [IsNoetherianRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]
    (z : ↥(AlgebraicCurve.TwoChartIntegralModel R F j)) :
    ringKrullDim ((AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.stalk z) ≤ ringKrullDim R + 1 := by sorry
