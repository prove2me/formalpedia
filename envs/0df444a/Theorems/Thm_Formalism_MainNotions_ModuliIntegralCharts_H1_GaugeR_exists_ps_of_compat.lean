-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GaugeR_exists_ps_of_compat
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.GaugeR.exists_ps_of_compat
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:23:33.510083+00:00
-- url     : https://prove2.me/theorems/cdfe14c3-e878-4e57-9852-50579e2f7ff0
-- title:
--   Gauge R: exists ps of compat
-- statement:
--   The Gauge R construction uses the exists ps of compat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/GaugeUniqB.lean#L113-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/GaugeUniqB.lean#L113-L136

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GaugeUniqA
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GaugeUniqB
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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1
open MvPolynomial Formalism.L2.Pj
open Formalism.MainNotions.ModuliIntegralCharts.H1.GaugeR
variable {R ι : Type} [CommRing R]
variable [Fintype ι] [DecidableEq ι]

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.GaugeR.exists_ps_of_compat (ρ : ∀ m, Jet R ι m) (h : ∀ m, jetTrunc (ρ (m + 1)) = ρ m) :
    ∃ r : MvPowerSeries ι R, ∀ m, psJet m r = ρ m := by sorry
