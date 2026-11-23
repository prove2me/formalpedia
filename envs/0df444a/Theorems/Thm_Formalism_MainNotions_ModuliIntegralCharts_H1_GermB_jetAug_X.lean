-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermB_jetAug_X
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.GermB.jetAug_X
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:04:18.930495+00:00
-- url     : https://prove2.me/theorems/349d5f30-29a5-4e32-8d9e-fca9cfdd4e5c
-- title:
--   Germ B: jet Aug X
-- statement:
--   The Germ B construction uses the jet Aug X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/GermBFr.lean#L85-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/GermBFr.lean#L85-L88

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermCut
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermDJet
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermBGen
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocalC
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermBFr
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

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.GermB.jetAug_X {Idx : Type} (m : ℕ) (q : Idx) :
    (jetAug : Jet S Idx m →ₐ[S] S) (Ideal.Quotient.mk _ (MvPolynomial.X q)) = 0 := by sorry
