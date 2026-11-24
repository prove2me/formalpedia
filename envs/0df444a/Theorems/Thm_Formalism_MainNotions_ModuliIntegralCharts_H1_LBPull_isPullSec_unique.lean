-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_LBPull_isPullSec_unique
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.LBPull.isPullSec_unique
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T10:02:29.985814+00:00
-- url     : https://prove2.me/theorems/e8f882c1-71f7-4306-a966-b6b3eb6ad91c
-- title:
--   LBPull: is Pull Sec unique
-- statement:
--   The LBPull construction uses the is Pull Sec unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/LBPull.lean#L41-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/LBPull.lean#L41-L48

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

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.LBPull.isPullSec_unique {T T' : Over S0} {h : T' ⊗ A ⟶ T ⊗ A} {hh : h ≫ snd T A = snd T' A}
    {s : LB.Sec (LPow A L a T)} {s' s'' : LB.Sec (LPow A L a T')}
    (h' : IsPullSec A L a h hh s s') (h'' : IsPullSec A L a h hh s s'') : s' = s'' := by sorry
