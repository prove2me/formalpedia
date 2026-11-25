-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermB_cgen_isGen
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.GermB.cgen_isGen
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:04:20.704844+00:00
-- url     : https://prove2.me/theorems/eb55a667-a114-47d7-897c-ecae54f62cdc
-- title:
--   Germ B: cgen is Gen
-- statement:
--   The Germ B construction uses the cgen is Gen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/GermBGen.lean#L52-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/GermBGen.lean#L52-L58

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocal
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_SubConstMemOrig
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermBGen
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
open AlgebraicGeometry CategoryTheory TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
variable {X Y : Scheme.{0}} (L : LB X) {K K' : Type} [Fintype K] [Fintype K']

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.GermB.cgen_isGen (hL : L.IsLB) (φ : K → (Y ⟶ X)) (ε : K → ℤ) (j0 : K → L.ι) (h0 : LB.wchart L φ j0 = ⊤) :
    (cgen L φ ε j0 h0).IsGen := by sorry
