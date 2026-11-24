-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_KAV_dAdd_single
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.KAV.dAdd_single
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T10:02:05.362652+00:00
-- url     : https://prove2.me/theorems/97b266af-d85d-4206-b1dd-67c7a6324131
-- title:
--   KAV: d Add single
-- statement:
--   The KAV construction uses the d Add single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ConstantCoeffPolyAdd.lean#L72-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ConstantCoeffPolyAdd.lean#L72-L80

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndEncPf
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IsExpChart
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_KillAdd
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ConstantCoeffPolyAdd
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
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open Formalism.MainNotions.ModuliIntegralCharts.H1.KAV
open MvPowerSeries

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.KAV.dAdd_single {S : Type} [CommRing S] {d n : ℕ} (j : Fin d) (b : Fin n) (G : Germ.PS S n d) :
    TB.dAdd (Pi.single j 1) b G = pderiv S (b, j) G := by sorry
