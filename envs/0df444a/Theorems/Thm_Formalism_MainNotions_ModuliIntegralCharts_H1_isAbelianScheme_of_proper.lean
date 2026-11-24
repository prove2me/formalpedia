-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_isAbelianScheme_of_proper
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.isAbelianScheme_of_proper
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T10:03:06.806354+00:00
-- url     : https://prove2.me/theorems/4cc802dd-2957-4e4d-a7ab-f66892687721
-- title:
--   H1: is Abelian Scheme of proper
-- statement:
--   The H1 construction uses the is Abelian Scheme of proper property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/PrimUniqPf.lean#L14-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/PrimUniqPf.lean#L14-L15

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_PrimUniqSt
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermFunPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBTransport
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_PrimUniqPf
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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1
open AlgebraicGeometry CategoryTheory NumberField TopologicalSpace Opposite MonoidalCategory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.isAbelianScheme_of_proper {S : Scheme.{0}} (G : Over S) [GrpObj G] (hs : IsSemiAbelian G)
    (hp : IsProper G.hom) : IsAbelianScheme G := by sorry
