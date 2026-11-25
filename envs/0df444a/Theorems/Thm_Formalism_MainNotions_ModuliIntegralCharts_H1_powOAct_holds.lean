-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_powOAct_holds
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.powOAct_holds
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T11:50:53.944328+00:00
-- url     : https://prove2.me/theorems/11aa9fd7-622f-51b5-80fe-3fc421cfbfa7
-- title:
--   H1: pow OAct holds
-- statement:
--   The H1 construction uses the pow OAct holds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/GPowPf.lean#L77-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/GPowPf.lean#L77-L102

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GPowSt
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GPowPf
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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.powOAct_holds (hR : BoxRosatiSt) (hT : BoxTauBalSt) : PowOActSt := by sorry
