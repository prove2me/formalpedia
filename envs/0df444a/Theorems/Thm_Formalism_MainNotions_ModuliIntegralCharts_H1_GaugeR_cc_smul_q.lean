-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GaugeR_cc_smul_q
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.GaugeR.cc_smul_q
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:40:47.149903+00:00
-- url     : https://prove2.me/theorems/876a1d40-336b-429d-9ee8-d4d5a7030677
-- title:
--   Gauge R: cc smul q
-- statement:
--   The Gauge R construction uses the cc smul q property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/GaugeExpPow.lean#L11-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/GaugeExpPow.lean#L11-L13

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CalcExp
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GaugeExpPow
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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.GaugeR
open ReciprocityTheory.ChartRestriction.G.TB.WickVanishing

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.GaugeR.cc_smul_q {S σ : Type} [CommRing S] {q : MvPowerSeries σ S} (hq : MvPowerSeries.constantCoeff q = 0)
    (r : S) : MvPowerSeries.constantCoeff (r • q) = 0 := by sorry
