-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_primUniq_of_global
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.primUniq_of_global
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T11:57:13.408093+00:00
-- url     : https://prove2.me/theorems/d035270b-dc36-5a27-ae79-fe0b77323183
-- title:
--   H1: prim Uniq of global
-- statement:
--   The H1 construction uses the prim Uniq of global property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/PrimUniqPf.lean#L170-L171
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/PrimUniqPf.lean#L170-L171

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_PrimUniqSt
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermFunPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBTransport
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_PrimUniqPf
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

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.primUniq_of_global (hglob : GlobalFnsSt) : PrimUniqSt := by sorry
