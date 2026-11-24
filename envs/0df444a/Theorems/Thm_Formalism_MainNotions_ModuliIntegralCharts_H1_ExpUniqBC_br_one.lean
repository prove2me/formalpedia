-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpUniqBC_br_one
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqBC.br_one
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T10:01:00.328724+00:00
-- url     : https://prove2.me/theorems/c086e442-e0b1-4a75-9cf9-5a9190cf8d51
-- title:
--   Exp Uniq BC: br one
-- statement:
--   The Exp Uniq BC construction uses the br one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ExpUniqBC.lean#L45-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ExpUniqBC.lean#L45-L46

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpUniqTan
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_UnivChartLoc
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpUniqBC
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Chart_comp_one__39cc6a6ed057
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_comp

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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqBC
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open MvPolynomial Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqJet Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqLoc Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqTan
open ReciprocityTheory.ChartRestriction.G.Chart (JetR zR IsUnivChart sp spMap spMap_comp comp_one')
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
variable {X : Scheme.{0}} (G : Over X) [GrpObj G] {S : Type} [CommRing S] (x0 : Sp S ⟶ X)
variable {G x0}

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqBC.br_one {A : Type} [CommRing A] [Algebra S A] : br G x0 (1 : overAt x0 A ⟶ G) = 1 := by sorry
