-- Prove2me | Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_connectedSpace_pullback_toBase_specMap_ratLocalizedAt
-- name    : AlgebraicCurve.TwoChartIntegralModel.connectedSpace_pullback_toBase_specMap_ratLocalizedAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.078526+00:00
-- url     : https://prove2.me/theorems/c07937a4-fe26-590a-83bc-daa34219499c
-- title:
--   Zariski connectedness for the two-chart integral model over ℤ_{(ℓ)}
-- statement:
--   Fix a prime $\ell$ and let $R = \mathbb{Z}_{(\ell)}$ be the subring [`GaloisRep.ratLocalizedAt ℓ`](def/GaloisRep_Flat.html#L8) of $\mathbb{Q}$ consisting of the rationals whose denominator is coprime to $\ell$. Let $F$ be a field that is an $R$-algebra and let $j \in F$ be nonzero. Write $A_{\mathrm{fin}}$, $A_{\infty}$, $A_{\mathrm{mid}}$ for the subalgebras `chartAlgFin`, `chartAlgInf`, `chartAlgMid` of $F$, namely the elements of $F$ integral over $R[j]$, over $R[j^{-1}]$ and over $R[j, j^{-1}]$ respectively, and let $X =$ `TwoChartIntegralModel R F j` be the pushout in schemes of $\operatorname{Spec} A_{\mathrm{mid}} \to \operatorname{Spec} A_{\mathrm{fin}}$ and $\operatorname{Spec} A_{\mathrm{mid}} \to \operatorname{Spec} A_{\infty}$ induced by the two inclusions, with structure morphism `toBase` $: X \to \operatorname{Spec} R$ obtained from the two maps $\operatorname{Spec} A_{\mathrm{fin}} \to \operatorname{Spec} R$, $\operatorname{Spec} A_{\infty} \to \operatorname{Spec} R$. Assume: (i) every $x \in F$ lying in both $A_{\mathrm{fin}}$ and $A_{\infty}$ is the image of some $r \in R$ under the structure map $R \to F$; (ii) the quotient of $A_{\mathrm{mid}}$ by the sum of the ranges of the two inclusion maps $A_{\mathrm{fin}} \to A_{\mathrm{mid}}$ and $A_{\infty} \to A_{\mathrm{mid}}$, as $R$-modules, is a finite $R$-module; (iii) `toBase` admits a section, i.e. there is $s : \operatorname{Spec} R \to X$ with $s$ followed by `toBase` the identity. Then for every field $L$ that is an $R$-algebra, the underlying topological space of the fibre product of `toBase` with $\operatorname{Spec}$ of the structure map $R \to L$ is a connected space.
--
--   This is a form of Zariski's connectedness principle, specialised to the two-chart integral model of a curve over the discrete valuation ring $\mathbb{Z}_{(\ell)}$: vanishing of the relevant $H^0$ beyond the constants together with finiteness of the two-chart Čech $H^1$ and the existence of a section forces all fibres, over fields of characteristic $0$ and of characteristic $\ell$ alike, to be connected. It is used for the model of the modular curve at $p$, via [`ModularCurve.XHDRModelAtP.connectedSpace_pullback_toBase_specMap_of_isAlgClosed`](thm.html#ModularCurve.XHDRModelAtP.connectedSpace_pullback_toBase_specMap_of_isAlgClosed).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_TwoChartIntegralModel_connectedSpace_pullback_toBase_specMap_ratLocalizedAt.lean

import Mathlib
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve

theorem AlgebraicCurve.TwoChartIntegralModel.connectedSpace_pullback_toBase_specMap_ratLocalizedAt
    (ℓ : ℕ) [Fact ℓ.Prime] (F : Type) [Field F] [Algebra ↥(GaloisRep.ratLocalizedAt ℓ) F] (j : F) [Fact (j ≠ 0)]
    (hconst : ∀ x : F, x ∈ TwoChartIntegralModel.chartAlgFin ↥(GaloisRep.ratLocalizedAt ℓ) F j →
      x ∈ TwoChartIntegralModel.chartAlgInf ↥(GaloisRep.ratLocalizedAt ℓ) F j →
      ∃ r : ↥(GaloisRep.ratLocalizedAt ℓ), algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) F r = x)
    (hfin : Module.Finite ↥(GaloisRep.ratLocalizedAt ℓ)
      (↥(TwoChartIntegralModel.chartAlgMid ↥(GaloisRep.ratLocalizedAt ℓ) F j) ⧸
        (LinearMap.range (TwoChartIntegralModel.inclFin ↥(GaloisRep.ratLocalizedAt ℓ) F j).toLinearMap ⊔
          LinearMap.range (TwoChartIntegralModel.inclInf ↥(GaloisRep.ratLocalizedAt ℓ) F j).toLinearMap)))
    (hsec : ∃ s : Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt ℓ)) ⟶ TwoChartIntegralModel ↥(GaloisRep.ratLocalizedAt ℓ) F j,
      s ≫ TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt ℓ) F j = 𝟙 _)
    (L : Type) [Field L] [Algebra ↥(GaloisRep.ratLocalizedAt ℓ) L] :
    ConnectedSpace ↥(pullback (TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt ℓ) F j)
      (Scheme.TwoAffineOpenCover.specMap ↥(GaloisRep.ratLocalizedAt ℓ) L)) := by sorry
