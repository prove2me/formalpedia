-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_LBPull_isValueAt_pull
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.LBPull.isValueAt_pull
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T10:03:09.871769+00:00
-- url     : https://prove2.me/theorems/4abccc54-5da7-4930-85a4-07de19db40a8
-- title:
--   LBPull: is Value At pull
-- statement:
--   The LBPull construction uses the is Value At pull property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/LBPull.lean#L64-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/LBPull.lean#L64-L93

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

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.LBPull.isValueAt_pull {T T' : Over S0} (g : T' ⟶ T) (z : T ⟶ A) {s : LB.Sec (LPow A L a T)}
    {s' : LB.Sec (LPow A L a T')} (hs : IsPullSec A L a (g ▷ A) (whiskerRight_snd g A) s s')
    {τ : LB.Gen (LB.LinComb L (Y := T.left) (K := Fin 1) (fun _ => z.left) (fun _ => a))} {v : Γ(T.left, ⊤)}
    (hv : IsValueAt A L a s z τ v) :
    IsValueAt A L a s' (g ≫ z) (LB.pullGen L (fun _ => z.left) (fun _ => a) τ g.left) (g.left.appTop.hom v) := by sorry
