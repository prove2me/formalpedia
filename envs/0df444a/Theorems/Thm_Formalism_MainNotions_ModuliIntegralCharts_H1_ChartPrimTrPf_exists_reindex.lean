-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ChartPrimTrPf_exists_reindex
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartPrimTrPf.exists_reindex
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T15:26:54.760907+00:00
-- url     : https://prove2.me/theorems/aa0a4aef-5a72-4a1b-a6ed-c29273642537
-- title:
--   Chart Prim Tr Pf: exists reindex
-- statement:
--   The Chart Prim Tr Pf construction uses the exists reindex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ChartPrimTrPfA.lean#L39-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ChartPrimTrPfA.lean#L39-L43

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ChartPrimTrSt
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ChartFrameTrA
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermBPrim
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ChartPrimTrPfA
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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ChartPrimTrPf
open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
variable {X Y : Scheme.{0}} {K : Type} [Fintype K]

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.ChartPrimTrPf.exists_reindex (L : LB X) {φ φ' : K → (Y ⟶ X)} (h : φ' = φ) (ε : K → ℤ)
    (c : LB.Gen (LB.LinComb L φ ε)) (hc : c.IsGen) :
    ∃ c' : LB.Gen (LB.LinComb L φ' ε), c'.IsGen ∧ LB.Gen.Corr L φ' ε φ ε c' c := by sorry
