-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_HarmInvC_sum_subst_quadCol
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.HarmInvC.sum_subst_quadCol
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T10:02:59.946259+00:00
-- url     : https://prove2.me/theorems/fce26bfb-9f14-4877-9315-cff5d8f1e928
-- title:
--   Harm Inv C: sum subst quad Col
-- statement:
--   The Harm Inv C construction uses the sum subst quad Col property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/HarmInvC.lean#L53-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/HarmInvC.lean#L53-L56

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

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.HarmInvC.sum_subst_quadCol (r : S) (β : Matrix (Fin d) (Fin d) S) :
    ∑ b : Fin n, MvPowerSeries.subst (sb b) (r • TB.quadCol (n := 1) β) = r • TB.quadCol (n := n) β := by sorry
