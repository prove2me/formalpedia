-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_tie_holds
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.tie_holds
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T10:03:26.529462+00:00
-- url     : https://prove2.me/theorems/85d607df-9f1d-400f-b380-6b2a3bffdf46
-- title:
--   H1: tie holds
-- statement:
--   The H1 construction uses the tie holds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ExpTiePf.lean#L328-L392
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ExpTiePf.lean#L328-L392

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpTieGerm
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndBCNab
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FBIdJet
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CalcExp
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpTiePf
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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField Formalism.L2.Pj
open MvPowerSeries ExpTieAlg ExpTieGerm ExpTiePf
attribute [local instance] Over.cartesianMonoidalCategory

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.tie_holds : TieSt := by sorry
