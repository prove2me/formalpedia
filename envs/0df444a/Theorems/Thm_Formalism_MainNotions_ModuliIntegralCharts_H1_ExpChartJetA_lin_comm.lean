-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpChartJetA_lin_comm
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.ExpChartJetA.lin_comm
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T09:58:51.448402+00:00
-- url     : https://prove2.me/theorems/822c46b0-8cf4-4408-b49c-cff32caa4d5c
-- title:
--   Exp Chart Jet A: lin comm
-- statement:
--   The Exp Chart Jet A construction uses the lin comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ExpChartJetA.lean#L184-L210
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ExpChartJetA.lean#L184-L210

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
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.ExpChartJetA.lin_comm {d : ℕ} (G : FGLaw R d) (u : Fin d → R) (k : Fin d) :
    ∑ j, u j * MvPowerSeries.coeff (Finsupp.single ((0 : Fin 2), j) 1) (G.F k) = u k := by sorry
