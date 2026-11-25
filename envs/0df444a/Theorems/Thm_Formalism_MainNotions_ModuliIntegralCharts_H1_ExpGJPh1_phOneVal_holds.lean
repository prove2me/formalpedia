-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGJPh1_phOneVal_holds
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGJPh1.phOneVal_holds
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T11:53:03.184025+00:00
-- url     : https://prove2.me/theorems/7f113f33-20ca-4a2f-973c-7d826d9c5fe2
-- title:
--   Exp GJPh1: ph One Val holds
-- statement:
--   The Exp GJPh1 construction uses the ph One Val holds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/SubstCoeRename.lean#L59-L173
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/SubstCoeRename.lean#L59-L173

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_PhOneValSt
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_SubstCoeRename
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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGJPh1
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open Formalism.MainNotions.ModuliIntegralCharts.H1.GermD Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGU Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGF Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGG Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGH
  Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGI
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGJPh1.phOneVal_holds : ExpGJ.PhOneValSt := by sorry
