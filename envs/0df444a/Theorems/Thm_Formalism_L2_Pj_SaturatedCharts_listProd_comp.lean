-- Prove2me | Theorems.Thm_Formalism_L2_Pj_SaturatedCharts_listProd_comp
-- name    : Formalism.L2.Pj.SaturatedCharts.listProd_comp
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T13:27:15.334811+00:00
-- url     : https://prove2.me/theorems/ac502b88-c4f2-4aff-bd0c-1248aaa34f17
-- title:
--   Saturated Charts: list Prod comp
-- statement:
--   The Saturated Charts construction uses the list Prod comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/SaturationChartsHolds.lean#L28-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/SaturationChartsHolds.lean#L28-L33

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ChartDirectionsIntegral
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExistsBasisOfSaturated
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_LieEig
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_ChartLaw
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_SaturationChartsHolds
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
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.SaturatedCharts
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
variable {S : Scheme.{0}} {M : Over S} [MonObj M]

theorem Formalism.L2.Pj.SaturatedCharts.listProd_comp {X : Over S} {N : Over S} [MonObj N] (g : M ⟶ N) [IsMonHom g] :
    ∀ {k : ℕ} (u : Fin k → (X ⟶ M)), (List.ofFn u).prod ≫ g = (List.ofFn fun i => u i ≫ g).prod
  := by sorry
