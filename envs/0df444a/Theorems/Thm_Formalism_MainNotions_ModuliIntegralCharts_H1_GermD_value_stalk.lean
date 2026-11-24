-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermD_value_stalk
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.GermD.value_stalk
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T10:01:56.581275+00:00
-- url     : https://prove2.me/theorems/a7ad8e1a-db08-4133-9224-44d87a55bb5f
-- title:
--   Germ D: value stalk
-- statement:
--   The Germ D construction uses the value stalk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/GermDVal.lean#L95-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/GermDVal.lean#L95-L103

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThetaPt
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermDVal
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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.GermD
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
variable {S0 : Scheme.{0}} (A : Over S0) [GrpObj A] (L : LB A.left)

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.GermD.value_stalk (hL : L.IsLB) (a : ℤ) {T : Over S0} {s : LB.Sec (LPow A L a T)} {z : T ⟶ A}
    {τ : LB.Gen (LB.LinComb L (Y := T.left) (K := Fin 1) (fun _ => z.left) (fun _ => a))} {v : Γ(T.left, ⊤)}
    (hv : IsValueAt A L a s z τ v) {Z : Scheme.{0}} (r : Z ⟶ T.left) (y : Z) (j : Fin 1 → L.ι)
    (hy : r y ∈ LB.wchart L (fun _ : Fin 1 => z.left) j) :
    gs (r ≫ (ptSecT A z).left) y _ (s.f j) = gs r y ⊤ v * (gm r y _ (τ.s j)).val := by sorry
