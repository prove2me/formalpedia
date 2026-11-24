-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_betaUniq_of_global
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.betaUniq_of_global
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T10:02:59.751717+00:00
-- url     : https://prove2.me/theorems/35eb1006-1b55-4f0f-9609-8e2c59774d3c
-- title:
--   H1: beta Uniq of global
-- statement:
--   The H1 construction uses the beta Uniq of global property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/GaugeBeta.lean#L39-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/GaugeBeta.lean#L39-L66

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IsExpChart
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_PrimUniqPf
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GaugeBeta
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
open AlgebraicGeometry CategoryTheory NumberField TopologicalSpace Opposite MonoidalCategory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.betaUniq_of_global (hglob : GlobalFnsSt) : BetaUniqSt := by sorry
