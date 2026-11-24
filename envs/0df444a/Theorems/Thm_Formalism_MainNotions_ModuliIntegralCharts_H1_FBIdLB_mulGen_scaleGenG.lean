-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_FBIdLB_mulGen_scaleGenG
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdLB.mulGen_scaleGenG
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:13:24.111003+00:00
-- url     : https://prove2.me/theorems/1cb1563e-fe67-4b15-aa02-7ba79a2e9e06
-- title:
--   FBId LB: mul Gen scale Gen G
-- statement:
--   The FBId LB construction uses the mul Gen scale Gen G property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/FBIdLB.lean#L46-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/FBIdLB.lean#L46-L54

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IsChartIff
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermDJet
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBCorr
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBTransport
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocal
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FBIdLB
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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdLB
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj NumberField
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} (t : SAB H X0)
variable {Y Z : Scheme.{0}} {K K' : Type} [Fintype K] [Fintype K']

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdLB.mulGen_scaleGenG (φ : K → (Y ⟶ t.G.left)) (ε : K → ℤ) (φ' : K' → (Y ⟶ t.G.left)) (ε' : K' → ℤ)
    (v v' : Γ(Y, ⊤)ˣ) (g : LB.Gen (LB.LinComb t.PP.L φ ε)) (g' : LB.Gen (LB.LinComb t.PP.L φ' ε')) :
    LB.mulGen t.PP.L φ ε φ' ε' (scaleGenG t φ ε v g) (scaleGenG t φ' ε' v' g') =
      scaleGenG t _ _ (v * v') (LB.mulGen t.PP.L φ ε φ' ε' g g') := by sorry
