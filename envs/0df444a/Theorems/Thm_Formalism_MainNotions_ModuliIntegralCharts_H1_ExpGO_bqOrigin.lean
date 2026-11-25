-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGO_bqOrigin
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGO.bqOrigin
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T11:53:52.720828+00:00
-- url     : https://prove2.me/theorems/6d196350-5f04-4b43-a216-d15bad5dc426
-- title:
--   Exp GO: bq Origin
-- statement:
--   The Exp GO construction uses the bq Origin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ExpGOPf.lean#L16-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ExpGOPf.lean#L16-L125

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_BqOriginSt
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpGOPf
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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGO
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 800000

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGO.bqOrigin : BqOriginSt := by sorry
