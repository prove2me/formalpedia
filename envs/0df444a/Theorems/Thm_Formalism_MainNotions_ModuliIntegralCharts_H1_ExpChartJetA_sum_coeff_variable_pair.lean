-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpChartJetA_sum_coeff_variable_pair
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.ExpChartJetA.sum_coeff_variable_pair
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T11:50:53.329564+00:00
-- url     : https://prove2.me/theorems/8d03e737-54d9-4a55-8554-438992651f5c
-- title:
--   Exp Chart Jet A: sum coeff variable pair
-- statement:
--   The Exp Chart Jet A construction uses the sum coeff variable pair property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ExpChartJetA.lean#L124-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ExpChartJetA.lean#L124-L138

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

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.ExpChartJetA.sum_coeff_variable_pair {κ₁ κ₂ : Type} [Fintype κ₁] [DecidableEq κ₁] [Fintype κ₂] [DecidableEq κ₂] (h : κ₁ → κ₂ → R)
    (s : κ₁ × κ₂) :
    ∑ i, ∑ j, h i j * MvPowerSeries.coeff (Finsupp.single (i, j) 1) (MvPowerSeries.X s : MvPowerSeries (κ₁ × κ₂) R) =
      h s.1 s.2 := by sorry
