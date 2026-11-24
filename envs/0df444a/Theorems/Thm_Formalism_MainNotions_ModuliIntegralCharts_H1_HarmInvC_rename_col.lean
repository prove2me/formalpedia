-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_HarmInvC_rename_col
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.HarmInvC.rename_col
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T10:03:04.832329+00:00
-- url     : https://prove2.me/theorems/5ea973e1-64eb-41e0-9704-f33548ca7555
-- title:
--   Harm Inv C: rename col
-- statement:
--   The Harm Inv C construction uses the rename col property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/HarmInvC.lean#L25-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/HarmInvC.lean#L25-L32

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_HarmInvA
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ConstantCoeffPolyAdd
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_PsiCover
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_KillAddFin
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_HarmInvC
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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.HarmInvC
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
variable {S : Type} [CommRing S] {n d : ℕ}

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.HarmInvC.rename_col (b : Fin n) (F : MvPowerSeries (Fin 1 × Fin d) S) :
    MvPowerSeries.rename (fun p : Fin 1 × Fin d => ((b, p.2) : Fin n × Fin d)) F = MvPowerSeries.subst (sb b) F := by sorry
