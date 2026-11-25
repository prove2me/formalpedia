-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_JetTr_psTrunc_map
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.JetTr.psTrunc_map
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T13:41:22.879905+00:00
-- url     : https://prove2.me/theorems/1c8168b7-4ba7-5f84-98b9-51e9f85488cd
-- title:
--   Jet Tr: ps Trunc map
-- statement:
--   The Jet Tr construction uses the ps Trunc map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ChartJetTrA.lean#L23-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ChartJetTrA.lean#L23-L25

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ChartTransportSt
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_SaturationChartsHolds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ChartJetTrA
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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.JetTr
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
variable {V K : Type} [CommRing V] [CommRing K] (f : V →+* K)

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.JetTr.psTrunc_map {σ : Type} [Fintype σ] [DecidableEq σ] (m : ℕ) (F : MvPowerSeries σ V) :
    psTrunc m (MvPowerSeries.map f F) = MvPolynomial.map f (psTrunc m F) := by sorry
