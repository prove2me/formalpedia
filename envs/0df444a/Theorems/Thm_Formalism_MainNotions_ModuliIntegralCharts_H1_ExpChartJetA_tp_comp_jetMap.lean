-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpChartJetA_tp_comp_jetMap
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.ExpChartJetA.tp_comp_jetMap
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T09:58:52.858801+00:00
-- url     : https://prove2.me/theorems/dc3c5365-7e5a-44ca-91a6-61794a6654ae
-- title:
--   Exp Chart Jet A: tp comp jet Map
-- statement:
--   The Exp Chart Jet A construction uses the tp comp jet Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ExpChartJetA.lean#L95-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ExpChartJetA.lean#L95-L110

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FBIdJet
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpChartJetA
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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpChartJetA
open Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdJet Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun Formalism.MainNotions.ModuliIntegralCharts.H1.GermD
variable {R : Type} [CommRing R]

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.ExpChartJetA.tp_comp_jetMap {κ κ' : Type} [Fintype κ'] [DecidableEq κ'] (h : κ' → R) (a : κ → MvPowerSeries κ' R)
    (ha : ∀ p, MvPowerSeries.constantCoeff (a p) = 0) :
    (tp h).comp (jetMap (m := 0 + 1) (fun p => psTrunc (0 + 1) (a p)) (fun p => psTrunc_mem_orig (0 + 1) (a p) (ha p))) =
      tp (fun p => ∑ q, h q * MvPowerSeries.coeff (Finsupp.single q 1) (a p)) := by sorry
