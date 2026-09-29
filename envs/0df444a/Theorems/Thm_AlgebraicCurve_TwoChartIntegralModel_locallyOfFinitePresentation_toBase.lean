-- Prove2me | Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_locallyOfFinitePresentation_toBase
-- name    : AlgebraicCurve.TwoChartIntegralModel.locallyOfFinitePresentation_toBase
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.26765+00:00
-- url     : https://prove2.me/theorems/a9029ae6-3631-5ded-a402-09129ab186d2
-- title:
--   Two-chart integral model is locally of finite presentation
-- statement:
--   Let $R$ be a commutative Noetherian ring, let $F$ be a field equipped with an $R$-algebra structure, and let $j \in F$ be nonzero. Write $A_{\mathrm{fin}} = \mathrm{chartAlgFin}\,R\,F\,j$ for the $R$-subalgebra of $F$ consisting of the elements of $F$ integral over $R[j] = \mathrm{Algebra.adjoin}\,R\,\{j\}$, and $A_{\infty} = \mathrm{chartAlgInf}\,R\,F\,j$ for the $R$-subalgebra of elements of $F$ integral over $R[j^{-1}]$; thus each is the integral closure in $F$ of the corresponding adjoined subalgebra. Assume both $A_{\mathrm{fin}}$ and $A_{\infty}$ are of finite type as $R$-algebras. The two-chart integral model $\mathcal{X} = \mathrm{TwoChartIntegralModel}\,R\,F\,j$ is the pushout, in schemes, of the two morphisms $\mathrm{Spec}$ of the inclusions of $A_{\mathrm{fin}}$ and of $A_{\infty}$ into the middle chart ring, and `toBase` is the morphism $\mathcal{X} \to \mathrm{Spec}\,R$ obtained from the universal property of this pushout from the two structure morphisms $\mathrm{Spec}\,A_{\mathrm{fin}} \to \mathrm{Spec}\,R$ and $\mathrm{Spec}\,A_{\infty} \to \mathrm{Spec}\,R$. The assertion is that `toBase` is locally of finite presentation.
--
--   This is the finite-presentation input for the two-chart integral model of a curve given by an affine coordinate $j$ and its inverse: over a Noetherian base, finite generation of the two chart algebras upgrades to finite presentation of the structure morphism. It is used by the smoothness and étale-coordinate criteria for this model, and by the integrality and local Noetherianity statements for Deligne–Rapoport-style models of modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_TwoChartIntegralModel_locallyOfFinitePresentation_toBase.lean

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

theorem AlgebraicCurve.TwoChartIntegralModel.locallyOfFinitePresentation_toBase
    (R : Type u) [CommRing R] [IsNoetherianRing R] (F : Type u) [Field F] [Algebra R F] (j : F)
    [Fact (j ≠ 0)]
    [Algebra.FiniteType R (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin R F j)]
    [Algebra.FiniteType R (AlgebraicCurve.TwoChartIntegralModel.chartAlgInf R F j)] :
    LocallyOfFinitePresentation (AlgebraicCurve.TwoChartIntegralModel.toBase R F j) := by sorry
