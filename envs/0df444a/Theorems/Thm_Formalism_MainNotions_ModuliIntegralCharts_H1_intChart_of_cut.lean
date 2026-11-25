-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_intChart_of_cut
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.intChart_of_cut
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:00:09.086729+00:00
-- url     : https://prove2.me/theorems/d4d0e47b-b15b-41e0-be42-9644f84822b8
-- title:
--   H1: int Chart of cut
-- statement:
--   The H1 construction uses the int Chart of cut property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/IntChartPf.lean#L16-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/IntChartPf.lean#L16-L25

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_IntChartSt
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_IntChartCut
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermCut
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermDPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_GlobFnsDvrPf
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_IntChartPf
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
open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.intChart_of_cut (hA : ChartDataGSt) (hB : FrameSt) (hC : FBIdSt) (hGF : GlobalFnsSt) :
    IntChartStatement := by sorry
