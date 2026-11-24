-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGH_ptm_congr
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGH.ptm_congr
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:28:47.121092+00:00
-- url     : https://prove2.me/theorems/0c185c90-042e-4635-bacf-097770ce4fa6
-- title:
--   Exp GH: ptm congr
-- statement:
--   The Exp GH construction uses the ptm congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ExpChartActionPoint.lean#L23-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ExpChartActionPoint.lean#L23-L29

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

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGH.ptm_congr (C : ChartAt Xo c y) {n : ℕ} {P P' : Fin n → Fin C.d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S}
    (hP : ∀ i j, MvPowerSeries.constantCoeff (P i j) = 0) (hP' : ∀ i j, MvPowerSeries.constantCoeff (P' i j) = 0)
    (m : ℕ) (h : ∀ i j, psJet m (P i j) = psJet m (P' i j)) : ptm C P m = ptm C P' m := by sorry
