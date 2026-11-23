-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermB_second_axis_at_second_copy
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.GermB.second_axis_at_second_copy
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T13:04:51.390581+00:00
-- url     : https://prove2.me/theorems/4fb82354-f894-4d59-8fb4-f8d7fc044364
-- title:
--   Germ B: second axis at second copy
-- statement:
--   The Germ B construction uses the second axis at second copy property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/GermBFr.lean#L119-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/GermBFr.lean#L119-L124

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermCut
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermDJet
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermBGen
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocalC
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermBFr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp

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
attribute [local instance] Over.cartesianMonoidalCategory
variable {S : Type} [CommRing S]
variable (d : ℕ)

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.GermB.second_axis_at_second_copy (m : ℕ) : (axis1 (S := S) d m).comp (jetCopy d m (1 : Fin 2)) =
    (Algebra.ofId S (Jet S (Fin 1 × Fin d) m)).comp jetAug := by sorry
