-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpChartJetA_sum_coeff_X_fst
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.ExpChartJetA.sum_coeff_X_fst
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T11:51:05.615352+00:00
-- url     : https://prove2.me/theorems/d29513b0-60d5-4cae-9d9e-3142d47cf94a
-- title:
--   Exp Chart Jet A: sum coeff X fst
-- statement:
--   The Exp Chart Jet A construction uses the sum coeff X fst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ExpChartJetA.lean#L140-L156
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ExpChartJetA.lean#L140-L156

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

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.ExpChartJetA.sum_coeff_X_fst {κ₁ κ₂ : Type} [Fintype κ₂] [DecidableEq κ₁] [DecidableEq κ₂] (u : κ₂ → R) (i : κ₁)
    (s : κ₁ × κ₂) :
    ∑ j, u j * MvPowerSeries.coeff (Finsupp.single (i, j) 1) (MvPowerSeries.X s : MvPowerSeries (κ₁ × κ₂) R) =
      if i = s.1 then u s.2 else 0 := by sorry
