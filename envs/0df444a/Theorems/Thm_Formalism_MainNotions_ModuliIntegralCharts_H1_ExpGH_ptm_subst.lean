-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGH_ptm_subst
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGH.ptm_subst
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:28:17.566934+00:00
-- url     : https://prove2.me/theorems/11483589-f453-4eaf-8910-107686ddbed0
-- title:
--   Exp GH: ptm subst
-- statement:
--   The Exp GH construction uses the ptm subst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ExpChartActionPoint.lean#L75-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ExpChartActionPoint.lean#L75-L86

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_HasSubstActPS
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpChartActionPoint
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGH
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open Formalism.MainNotions.ModuliIntegralCharts.H1.GermD Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGU Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGF Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGG
attribute [local instance] Over.cartesianMonoidalCategory
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]
variable {S : Type} [CommRing S] [Algebra c.F S] [Algebra ℚ S] {y : FrPt Xo c S}

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGH.ptm_subst (C : ChartAt Xo c y) {n n' : ℕ} (P : Fin n → Fin C.d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S)
    (hP : ∀ i j, MvPowerSeries.constantCoeff (P i j) = 0) (m : ℕ)
    (σ : Fin n' × Fin C.d → MvPolynomial (Fin n × Fin C.d) S) (hσ : ∀ k, MvPolynomial.constantCoeff (σ k) = 0) :
    ptm C P m ≫ homAt y.x (jetSubstP m σ) =
      ptm C (fun i j => MvPowerSeries.subst (fun p : Fin n × Fin C.d => P p.1 p.2)
        ((σ (i, j) : MvPolynomial _ S) : MvPowerSeries (Fin n × Fin C.d) S)) m := by sorry
