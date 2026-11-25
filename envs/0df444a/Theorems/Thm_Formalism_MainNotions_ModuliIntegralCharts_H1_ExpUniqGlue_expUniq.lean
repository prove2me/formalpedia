-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpUniqGlue_expUniq
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqGlue.expUniq
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T13:39:16.381688+00:00
-- url     : https://prove2.me/theorems/d626e516-7400-41d4-afa6-0cd66eaacb36
-- title:
--   Exp Uniq Glue: exp Uniq
-- statement:
--   The Exp Uniq Glue construction uses the exp Uniq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ExpUniqGlue.lean#L244-L246
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ExpUniqGlue.lean#L244-L246

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpUniqBC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_JetGlue
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_EigLatBasis
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpUniqGlue
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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqGlue
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open MvPolynomial Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqJet
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqGlue.expUniq : ExpUniqSt := by sorry
