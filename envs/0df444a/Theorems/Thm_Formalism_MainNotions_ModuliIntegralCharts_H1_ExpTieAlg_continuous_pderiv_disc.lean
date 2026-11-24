-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpTieAlg_continuous_pderiv_disc
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.ExpTieAlg.continuous_pderiv_disc
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T09:59:54.760201+00:00
-- url     : https://prove2.me/theorems/6eddf4c9-6c49-4d60-97fb-b5473c01416e
-- title:
--   Exp Tie Alg: continuous pderiv disc
-- statement:
--   The Exp Tie Alg construction uses the continuous pderiv disc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ExpTieAlg.lean#L15-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ExpTieAlg.lean#L15-L20

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpTie
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_MonoVal
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpTieAlg
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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpTieAlg
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {S : Type} [CommRing S]
open scoped MvPowerSeries.WithPiTopology

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.ExpTieAlg.continuous_pderiv_disc {σ R : Type} [CommRing R] [TopologicalSpace R] [DiscreteTopology R]
    (i : σ) : Continuous (fun f : MvPowerSeries σ R => pderiv R i f) := by sorry
