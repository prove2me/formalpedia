-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_LBPull_shape_rig
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.LBPull.shape_rig
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T10:02:27.977824+00:00
-- url     : https://prove2.me/theorems/ccff19f2-0a4c-4308-88cf-66027f06a43f
-- title:
--   LBPull: shape rig
-- statement:
--   The LBPull construction uses the shape rig property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/LBPull.lean#L106-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/LBPull.lean#L106-L114

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

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.LBPull.shape_rig {X T T' : Scheme.{0}} (g : T' ⟶ T) (f : T ⟶ X) (f' : T' ⟶ X) (hf : g ≫ f = f')
    {U : X.Opens} {W : T.Opens} (hW : W ≤ f ⁻¹ᵁ U) {V : T'.Opens} (hV : V ≤ g ⁻¹ᵁ W) {V' : T'.Opens}
    (hV' : V' ≤ f' ⁻¹ᵁ U) {O : T'.Opens} (o1 : O ≤ V) (o2 : O ≤ V') (x : Γ(X, U)ˣ) (k : ℤ) :
    res o1 (res hV (pullU g W ((res hW (pullU f U x)) ^ k))) = res o2 ((res hV' (pullU f' U x)) ^ k) := by sorry
