-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_CIndFrFix3_psJet_coe_trunc
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix3.psJet_coe_trunc
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T11:52:54.571041+00:00
-- url     : https://prove2.me/theorems/a3e526f3-85e1-4142-b1fa-67a69c7d225a
-- title:
--   CInd Fr Fix3: ps Jet coe trunc
-- statement:
--   The CInd Fr Fix3 construction uses the ps Jet coe trunc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/EvalSinglePointId.lean#L22-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/EvalSinglePointId.lean#L22-L36

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndFrFix
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpTiePf
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_JetSubstPSTrunc
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_EvalSinglePointId
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_CZ_pt

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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix3
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw FB)
attribute [local instance] Over.cartesianMonoidalCategory
variable {S : Type} [CommRing S] {d : ℕ}

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix3.psJet_coe_trunc {κ : Type} [Fintype κ] [DecidableEq κ] (m : ℕ) (g : MvPowerSeries κ S) :
    psJet m ((psTrunc m g : MvPolynomial κ S) : MvPowerSeries κ S) = psJet m g := by sorry
