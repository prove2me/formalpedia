-- Prove2me | Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_isIntegral
-- name    : AlgebraicCurve.TwoChartIntegralModel.isIntegral
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.26765+00:00
-- url     : https://prove2.me/theorems/967f27b8-d882-53f1-b108-0584b6a122e6
-- title:
--   The two-chart integral model is integral
-- statement:
--   Let $R$ be a commutative ring, let $F$ be a field equipped with an $R$-algebra structure, and let $j \in F$ be nonzero. Consider the two-chart integral model [`AlgebraicCurve.TwoChartIntegralModel R F j`](def/AlgebraicCurve_TwoChartIntegralModel.html#L236), which by definition is the pushout, in the category of schemes, of the pair of morphisms $f_{\mathrm{Fin}} \colon X_{\mathrm{Mid}} \to X_{\mathrm{Fin}}$ and $f_{\mathrm{Inf}} \colon X_{\mathrm{Mid}} \to X_{\mathrm{Inf}}$, where $f_{\mathrm{Fin}}$ is $\operatorname{Spec}$ applied to the ring homomorphism underlying the algebra map `inclFin R F j` and $f_{\mathrm{Inf}}$ is $\operatorname{Spec}$ applied to the ring homomorphism underlying `inclInf R F j` (the two charts are spectra of the chart algebras `chartAlg R F S`, subalgebras of $F$, and $X_{\mathrm{Mid}}$ is their common overlap). The assertion is that this scheme is integral in the sense of Mathlib's `IsIntegral`, that is, its underlying topological space is irreducible and the scheme is reduced. No hypothesis beyond commutativity is imposed on $R$, and no finiteness or flatness assumption is made.
--
--   Integrality of the glued two-chart model over an arbitrary base ring $R$; it is the base-generic form of the integrality of the Igusa-type model of a modular curve obtained by gluing the $j$ and $1/j$ charts along their overlap. It is used downstream by the statements about chart pinning, étale coordinates at points of residue characteristic conditions, and recognition of isomorphisms of such models.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_TwoChartIntegralModel_isIntegral.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve.TwoChartIntegralModel

universe u
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

theorem AlgebraicCurve.TwoChartIntegralModel.isIntegral
    (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)] :
    IsIntegral (AlgebraicCurve.TwoChartIntegralModel R F j) := by sorry
