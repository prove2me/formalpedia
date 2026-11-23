-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpTieAlg_dof_addF
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.ExpTieAlg.dof_addF
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T13:47:58.668792+00:00
-- url     : https://prove2.me/theorems/585aef1c-6af9-4b39-89cd-ba661c9d5232
-- title:
--   Exp Tie Alg: dof add F
-- statement:
--   The Exp Tie Alg construction uses the dof add F property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ExpTieAlg.lean#L129-L149
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ExpTieAlg.lean#L129-L149

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
variable {N d : ℕ}

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.ExpTieAlg.dof_addF (u : Fin N → S) (g : PS S 1 N) :
    Dof (ReciprocityTheory.ChartRestriction.G.TB.MV.addF S N) u g = ∑ j, C (u j) * pderiv S ((0 : Fin 1), j) g := by sorry
