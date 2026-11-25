-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_LBPull_isPullSec_id
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.LBPull.isPullSec_id
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T11:53:03.290734+00:00
-- url     : https://prove2.me/theorems/2a768bb3-2292-4787-ac1d-f6414885d372
-- title:
--   LBPull: is Pull Sec id
-- statement:
--   The LBPull construction uses the is Pull Sec id property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/LBPull.lean#L145-L152
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/LBPull.lean#L145-L152

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FBIdLB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThetaPt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_LBPull
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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.LBPull
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj NumberField
attribute [local instance] Over.cartesianMonoidalCategory
variable {S0 : Scheme.{0}} (A : Over S0) [GrpObj A] (L : LB A.left) (a : ℤ)

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.LBPull.isPullSec_id {T : Over S0} (hh : 𝟙 (T ⊗ A) ≫ snd T A = snd T A) (s : LB.Sec (LPow A L a T)) :
    IsPullSec A L a (𝟙 (T ⊗ A)) hh s s := by sorry
