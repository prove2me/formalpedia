-- Prove2me | Theorems.Thm_Formalism_L2_Pj_SaturatedCharts_comp_listProd
-- name    : Formalism.L2.Pj.SaturatedCharts.comp_listProd
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T13:28:19.045532+00:00
-- url     : https://prove2.me/theorems/fe3503c8-2b7d-41e3-87a0-a2ab930db2d7
-- title:
--   Saturated Charts: comp list Prod
-- statement:
--   The Saturated Charts construction uses the comp list Prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/SaturationChartsHolds.lean#L21-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/SaturationChartsHolds.lean#L21-L26

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

theorem Formalism.L2.Pj.SaturatedCharts.comp_listProd {X Y : Over S} (f : X ⟶ Y) : ∀ {k : ℕ} (u : Fin k → (Y ⟶ M)),
    f ≫ (List.ofFn u).prod = (List.ofFn fun i => f ≫ u i).prod
  := by sorry
