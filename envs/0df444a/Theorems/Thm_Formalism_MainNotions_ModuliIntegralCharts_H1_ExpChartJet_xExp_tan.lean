-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpChartJet_xExp_tan
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.ExpChartJet.xExp_tan
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T09:59:11.556791+00:00
-- url     : https://prove2.me/theorems/548cbba6-dd0f-4895-9a9d-07c3c07eb057
-- title:
--   Exp Chart Jet: x Exp tan
-- statement:
--   The Exp Chart Jet construction uses the x Exp tan property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ExpChartJet.lean#L396-L436
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ExpChartJet.lean#L396-L436

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpTie
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FBIdJet
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpChartJetA
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpChartJet
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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpChartJet
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField Formalism.L2.Pj
open Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdJet Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun Formalism.MainNotions.ModuliIntegralCharts.H1.GermD
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.ExpChartJetA
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]
variable {S : Type} [CommRing S] [Algebra c.F S] [Algebra ℚ S] {y : FrPt Xo c S}
variable (C : ChartAt Xo c y)
variable (φ : Fin C.d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S)

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.ExpChartJet.xExp_tan (hφ : IsExpOf C.B.G.F C.uvec φ) (ℓ : Lt1 Dw) : IsCombAt y.x
    (fun j : Fin (dL Dw) => (homAt y.x (jetTan ((0 : Fin 1), j) :
      Jet S (Fin 1 × Fin (dL Dw)) (0 + 1) →ₐ[S] DualNumber S) ≫ xExp y C φ 1).left)
    (fun j => if j = ltIdx Dw ℓ then 1 else 0) (y.u ℓ.1 ℓ.2) := by sorry
