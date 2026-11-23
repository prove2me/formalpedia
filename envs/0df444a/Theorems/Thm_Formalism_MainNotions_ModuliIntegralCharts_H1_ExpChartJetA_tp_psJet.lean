-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpChartJetA_tp_psJet
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.ExpChartJetA.tp_psJet
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T13:39:37.753916+00:00
-- url     : https://prove2.me/theorems/901ba2b0-b32c-4dd5-808f-bcc3d8a951ca
-- title:
--   Exp Chart Jet A: tp ps Jet
-- statement:
--   The Exp Chart Jet A construction uses the tp ps Jet property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ExpChartJetA.lean#L70-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ExpChartJetA.lean#L70-L79

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

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.ExpChartJetA.tp_psJet {κ : Type} [Fintype κ] [DecidableEq κ] (g : κ → R) (f : MvPowerSeries κ R) :
    tp g (psJet (0 + 1) f) = TrivSqZeroExt.inl (MvPowerSeries.constantCoeff f) +
      TrivSqZeroExt.inr (∑ q, g q * MvPowerSeries.coeff (Finsupp.single q 1) f) := by sorry
