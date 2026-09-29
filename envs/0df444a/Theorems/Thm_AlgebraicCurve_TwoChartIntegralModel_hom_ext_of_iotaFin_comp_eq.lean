-- Prove2me | Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_hom_ext_of_iotaFin_comp_eq
-- name    : AlgebraicCurve.TwoChartIntegralModel.hom_ext_of_iotaFin_comp_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.26765+00:00
-- url     : https://prove2.me/theorems/aeda0acb-3c02-592d-bb1f-124b06e0ce34
-- title:
--   Rigidity of maps from the two-chart integral model
-- statement:
--   Fix a commutative ring $R$, a field $F$ carrying an $R$-algebra structure, and an element $j \in F$ with $j \neq 0$, and let $\mathfrak X =$ [`AlgebraicCurve.TwoChartIntegralModel R F j`](def/AlgebraicCurve_TwoChartIntegralModel.html#L236) be the scheme obtained as the pushout, in the category of schemes, of the two morphisms of affine schemes $\mathrm{Spec}$ applied to the ring maps underlying `inclFin R F j` and `inclInf R F j`, namely `fFin R F j` $: X_{\mathrm{Mid}} \to X_{\mathrm{Fin}}$ and `fInf R F j` $: X_{\mathrm{Mid}} \to X_{\mathrm{Inf}}$. Let $Y$ and $Z$ be schemes, let $f, g : \mathfrak X \to Y$ be two morphisms, and let $q : Y \to Z$ be a separated morphism. Assume that $f$ and $g$ become equal after composition with $q$, i.e. $q \circ f = q \circ g$ as morphisms $\mathfrak X \to Z$, and that $f$ and $g$ agree after precomposition with the morphism `ιFin R F j` onto the $j$-finite chart of $\mathfrak X$, i.e. $f \circ \iota_{\mathrm{Fin}} = g \circ \iota_{\mathrm{Fin}}$. Then $f = g$.
--
--   This is the standard rigidity (uniqueness) principle for morphisms out of an integral scheme into a scheme separated over a base: two such morphisms that agree on a dense open chart coincide. It is the tool used to identify morphisms out of the two-chart integral model by their effect on the $j$-finite chart alone, and is invoked in the construction of the Deligne–Rapoport type models of modular curves, for instance in the identification of Atkin–Lehner and Hecke degeneracy data and of Galois-equivariant point maps on `ModularCurve.XOneP`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_TwoChartIntegralModel_hom_ext_of_iotaFin_comp_eq.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve AlgebraicCurve.TwoChartIntegralModel

theorem AlgebraicCurve.TwoChartIntegralModel.hom_ext_of_iotaFin_comp_eq
    (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]
    {Y Z : Scheme.{u}} (f g : AlgebraicCurve.TwoChartIntegralModel R F j ⟶ Y) (q : Y ⟶ Z) [IsSeparated q]
    (h : f ≫ q = g ≫ q) (hFin : ιFin R F j ≫ f = ιFin R F j ≫ g) : f = g := by sorry
