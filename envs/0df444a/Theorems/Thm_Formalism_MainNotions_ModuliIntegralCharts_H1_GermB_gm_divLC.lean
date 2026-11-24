-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermB_gm_divLC
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.GermB.gm_divLC
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T10:01:12.47184+00:00
-- url     : https://prove2.me/theorems/8ddda315-491f-46ad-8f99-8977b9079061
-- title:
--   Germ B: gm div LC
-- statement:
--   The Germ B construction uses the gm div LC property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/GermBGen.lean#L95-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/GermBGen.lean#L95-L104

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

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.GermB.gm_divLC (φ : K → (Y ⟶ X)) (ε : K → ℤ) (φ' : K' → (Y ⟶ X)) (ε' : K' → ℤ)
    (p q : (K → L.ι) × (K' → L.ι)) (y : Y) (hp : (𝟙 Y : Y ⟶ Y) y ∈ (LB.div (LB.LinComb L φ ε) (LB.LinComb L φ' ε')).U p)
    (hq : (𝟙 Y : Y ⟶ Y) y ∈ (LB.div (LB.LinComb L φ ε) (LB.LinComb L φ' ε')).U q) :
    gm (𝟙 Y) y _ ((LB.div (LB.LinComb L φ ε) (LB.LinComb L φ' ε')).g p q) =
      trF φ ε (𝟙 Y) y p.1 q.1 * (trF φ' ε' (𝟙 Y) y p.2 q.2)⁻¹ := by sorry
