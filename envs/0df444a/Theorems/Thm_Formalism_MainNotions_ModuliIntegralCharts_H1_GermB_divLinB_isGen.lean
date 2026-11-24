-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermB_divLinB_isGen
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.GermB.divLinB_isGen
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T10:01:51.515272+00:00
-- url     : https://prove2.me/theorems/d685d5f5-a0b5-4c2a-81b9-f8f080b8785c
-- title:
--   Germ B: div Lin B is Gen
-- statement:
--   The Germ B construction uses the div Lin B is Gen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/GermBPrim.lean#L26-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/GermBPrim.lean#L26-L51

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermBSer
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermBPrim
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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.GermB
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1.GermD
open Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun
attribute [local instance] Over.cartesianMonoidalCategory
variable {X : Scheme.{0}} (L : LB X) {K : Type} [Fintype K]

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.GermB.divLinB_isGen (φ : K → (X ⟶ X)) (ε : K → ℤ) (w : LB.Gen (LB.div (LB.LinComb L φ ε) L)) (hw : w.IsGen) :
    (divLinB L φ ε w).IsGen := by sorry
