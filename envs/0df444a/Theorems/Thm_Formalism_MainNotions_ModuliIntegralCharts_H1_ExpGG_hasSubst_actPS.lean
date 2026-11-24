-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGG_hasSubst_actPS
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGG.hasSubst_actPS
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:22:09.912845+00:00
-- url     : https://prove2.me/theorems/dfda8578-8522-4c6d-8a01-e8c3dcd1efa4
-- title:
--   Exp GG: has Subst act PS
-- statement:
--   The Exp GG construction uses the has Subst act PS property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/HasSubstActPS.lean#L19-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/HasSubstActPS.lean#L19-L20

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_JetSubstPSEqJetMap
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_UnitIdSt
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_HasSubstActPS
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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGG
open MvPowerSeries NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGU
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {S : Type} [CommRing S] (c : Coeff l) [Algebra c.F S]

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGG.hasSubst_actPS (a : 𝓞 E) : HasSubst (actPS (Dw := Dw) (S := S) c a) := by sorry
