-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_LBPull_isPullSec_comp
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.LBPull.isPullSec_comp
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T10:03:03.016145+00:00
-- url     : https://prove2.me/theorems/5461b7d9-ef47-4358-9ad4-e6a420de44bc
-- title:
--   LBPull: is Pull Sec comp
-- statement:
--   The LBPull construction uses the is Pull Sec comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/LBPull.lean#L134-L143
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/LBPull.lean#L134-L143

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

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.LBPull.isPullSec_comp {T T' T'' : Over S0} {h : T' ⊗ A ⟶ T ⊗ A} {hh : h ≫ snd T A = snd T' A}
    {h' : T'' ⊗ A ⟶ T' ⊗ A} {hh' : h' ≫ snd T' A = snd T'' A}
    {s : LB.Sec (LPow A L a T)} {s' : LB.Sec (LPow A L a T')} {s'' : LB.Sec (LPow A L a T'')}
    (h1 : IsPullSec A L a h hh s s') (h2 : IsPullSec A L a h' hh' s' s'') :
    IsPullSec A L a (h' ≫ h) (by rw [Category.assoc, hh, hh']) s s'' := by sorry
