-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GaugeR_psJet_pow
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.GaugeR.psJet_pow
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T10:01:26.542941+00:00
-- url     : https://prove2.me/theorems/cf91a2cf-8b1b-4a2b-b87b-faef73cfe6b4
-- title:
--   Gauge R: ps Jet pow
-- statement:
--   The Gauge R construction uses the ps Jet pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/GaugeUniqB.lean#L62-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/GaugeUniqB.lean#L62-L65

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

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.GaugeR.psJet_pow (m : ℕ) (f : MvPowerSeries ι R) (k : ℕ) : psJet m (f ^ k) = psJet m f ^ k := by sorry
