-- Prove2me | Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_hom_comm_and_hom_comp_hom_eq_of_chartPins
-- name    : AlgebraicCurve.TwoChartIntegralModel.hom_comm_and_hom_comp_hom_eq_of_chartPins
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.26765+00:00
-- url     : https://prove2.me/theorems/fda91124-329c-5dc7-8e1f-1975020b4a18
-- title:
--   Pinned automorphisms of the two-chart model: commuting and squaring
-- statement:
--   Let $R$ be a commutative ring, $F$ a field with an $R$-algebra structure, and $j \in F$ a nonzero element, and assume that the structure morphism $\mathrm{toBase}\,R\,F\,j$ of the two-chart integral model $\mathfrak X = \mathrm{TwoChartIntegralModel}\,R\,F\,j$ — the pushout of `fFin R F j` and `fInf R F j`, mapped to $\operatorname{Spec} R$ by the two chart structure maps — is separated. Here the finite chart algebra `chartAlgFin R F j` is the $R$-subalgebra of $F$ consisting of the elements integral over $R[j]$, and `ιFin R F j` denotes the chart morphism from its spectrum into $\mathfrak X$. Let $w, \delta : \mathfrak X \cong \mathfrak X$ be isomorphisms with $w.\mathrm{hom}$ and $\delta.\mathrm{hom}$ both commuting with $\mathrm{toBase}\,R\,F\,j$, and let $\theta_w, \theta_\delta$ be $R$-algebra endomorphisms of `chartAlgFin R F j` pinning them on the finite chart, in the two directions $\iota_{\mathrm{fin}} \text{ followed by } w.\mathrm{hom} = \operatorname{Spec}(\theta_w) \text{ followed by } \iota_{\mathrm{fin}}$ and $\operatorname{Spec}(\theta_\delta) \text{ followed by } \iota_{\mathrm{fin}} = \iota_{\mathrm{fin}} \text{ followed by } \delta.\mathrm{inv}$. The conclusion is the conjunction of two implications: if $\theta_w \circ \theta_\delta = \theta_\delta \circ \theta_w$ pointwise, then $w.\mathrm{hom}$ and $\delta.\mathrm{hom}$ commute; and if $\theta_\delta(\theta_w(\theta_w(x))) = x$ for all $x$, then $w.\mathrm{hom}$ followed by $w.\mathrm{hom}$ equals $\delta.\mathrm{hom}$.
--
--   This is a rigidity (pinning) lemma: relations among automorphisms of the two-chart integral model over $\operatorname{Spec} R$ are detected by the corresponding relations among their chart endomorphisms on the finite chart. It is used to transport the Atkin–Lehner involution and diamond relations, verified as identities of algebra maps on the finite chart, to the integral model of a modular curve, and is cited by [`ModularCurve.exists_xHDRModelAtP_atkinLehner_generic_chart`](thm.html#ModularCurve.exists_xHDRModelAtP_atkinLehner_generic_chart).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_TwoChartIntegralModel_hom_comm_and_hom_comp_hom_eq_of_chartPins.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve AlgebraicCurve.TwoChartIntegralModel

theorem AlgebraicCurve.TwoChartIntegralModel.hom_comm_and_hom_comp_hom_eq_of_chartPins
    (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]
    [IsSeparated (toBase R F j)]
    (w : AlgebraicCurve.TwoChartIntegralModel R F j ≅ AlgebraicCurve.TwoChartIntegralModel R F j)
    (hw : w.hom ≫ toBase R F j = toBase R F j)
    (θw : ↥(chartAlgFin R F j) →ₐ[R] ↥(chartAlgFin R F j))
    (hpw : ιFin R F j ≫ w.hom = Spec.map (CommRingCat.ofHom θw.toRingHom) ≫ ιFin R F j)
    (δ : AlgebraicCurve.TwoChartIntegralModel R F j ≅ AlgebraicCurve.TwoChartIntegralModel R F j)
    (hδ : δ.hom ≫ toBase R F j = toBase R F j)
    (θδ : ↥(chartAlgFin R F j) →ₐ[R] ↥(chartAlgFin R F j))
    (hpδ : Spec.map (CommRingCat.ofHom θδ.toRingHom) ≫ ιFin R F j = ιFin R F j ≫ δ.inv) :
    ((∀ x, θw (θδ x) = θδ (θw x)) → w.hom ≫ δ.hom = δ.hom ≫ w.hom) ∧
    ((∀ x, θδ (θw (θw x)) = x) → w.hom ≫ w.hom = δ.hom) := by sorry
