-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_HarmInvB_subst_lg
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.HarmInvB.subst_lg
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T10:02:43.912251+00:00
-- url     : https://prove2.me/theorems/2dc332cc-3efd-412b-8ff2-4120aa5c5acb
-- title:
--   Harm Inv B: subst lg
-- statement:
--   The Harm Inv B construction uses the subst lg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/HarmInvB.lean#L147-L175
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/HarmInvB.lean#L147-L175

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndFrFix
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpOfPf
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_HarmInvA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CalcAdd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_KillAdd
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_HarmInvB
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
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.HarmInvB.subst_lg (G : FGLaw S d) {τ : Type} (Bφ : Fin 2 × Fin d → MvPowerSeries τ S)
    (hB : ∀ p, MvPowerSeries.constantCoeff (Bφ p) = 0) (j : Fin 2) (i : Fin d) :
    MvPowerSeries.subst Bφ (lg G j i) = MvPowerSeries.subst (fun p : Fin 1 × Fin d => Bφ (j, p.2)) (logOf G i) := by sorry
