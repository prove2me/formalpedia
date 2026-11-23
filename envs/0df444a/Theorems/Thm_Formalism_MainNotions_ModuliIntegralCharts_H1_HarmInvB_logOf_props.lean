-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_HarmInvB_logOf_props
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.HarmInvB.logOf_props
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T14:07:18.104663+00:00
-- url     : https://prove2.me/theorems/6e3f2805-cb7c-45a9-a94b-a9e6d661a497
-- title:
--   Harm Inv B: log Of props
-- statement:
--   The Harm Inv B construction uses the log Of props property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/HarmInvB.lean#L23-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/HarmInvB.lean#L23-L59

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndFrFix
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpOfPf
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_HarmInvA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CalcAdd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_KillAdd
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_HarmInvB
import Theorems.Thm_Formalism_FG_InjVAux_HasOrd_add
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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.HarmInvB
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB Formalism.L2.Pj NumberField
open Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix Formalism.MainNotions.ModuliIntegralCharts.H1.ExpOf Formalism.MainNotions.ModuliIntegralCharts.H1.HarmInvA
open ReciprocityTheory.ChartRestriction.G.TB.LogPf (logOf)
variable {S : Type} [CommRing S] [Algebra ℚ S] {d : ℕ}
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.TB.LogPf

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.HarmInvB.logOf_props (G : FGLaw S d) :
    (∀ i, constantCoeff ((fun i => logOf G i) i) = 0) ∧ dLin (fun i => logOf G i) = 1 ∧
    comp1 (fun i => logOf G i) (G.add (pt S (n := 2) d 0) (pt S (n := 2) d 1)) =
      comp1 (fun i => logOf G i) (pt S (n := 2) d 0) + comp1 (fun i => logOf G i) (pt S (n := 2) d 1) := by sorry
