-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_LBPull_isPullSec_congr
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.LBPull.isPullSec_congr
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:10:17.384795+00:00
-- url     : https://prove2.me/theorems/c109abff-b07d-498d-9c38-4c5ce6e00f28
-- title:
--   LBPull: is Pull Sec congr
-- statement:
--   The LBPull construction uses the is Pull Sec congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/LBPull.lean#L34-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/LBPull.lean#L34-L39

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

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.LBPull.isPullSec_congr {T T' : Over S0} {h₁ h₂ : T' ⊗ A ⟶ T ⊗ A} (e : h₁ = h₂)
    (hh₁ : h₁ ≫ snd T A = snd T' A) (hh₂ : h₂ ≫ snd T A = snd T' A)
    (s : LB.Sec (LPow A L a T)) (s' : LB.Sec (LPow A L a T')) :
    IsPullSec A L a h₁ hh₁ s s' ↔ IsPullSec A L a h₂ hh₂ s s' := by sorry
