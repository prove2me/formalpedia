-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_harmLink_holds
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.harmLink_holds
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T11:57:44.565272+00:00
-- url     : https://prove2.me/theorems/cf123132-7f46-5734-8f51-e787830844e7
-- title:
--   H1: harm Link holds
-- statement:
--   The H1 construction uses the harm Link holds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/CIndEncPf.lean#L29-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/CIndEncPf.lean#L29-L45

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndEnc
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndEncPf
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
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open CIndEncPf

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.harmLink_holds : HarmLinkSt := by sorry
