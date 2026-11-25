-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_FormalGroupCopies_dofN_mem
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.FormalGroupCopies.dofN_mem
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T01:10:07.342033+00:00
-- url     : https://prove2.me/theorems/15038cb7-efbe-4564-aa0a-e38fe8056809
-- title:
--   Formal Group Copies: dof N mem
-- statement:
--   The Formal Group Copies construction uses the dof N mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/FormalGroupCopies.lean#L81-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/FormalGroupCopies.lean#L81-L86

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FormalGroupOnCopies
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_PartialDerivativeExponent
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FormalGroupCopies
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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.FormalGroupCopies
open MvPowerSeries Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open Formalism.MainNotions.ModuliIntegralCharts.H1.FormalGroupOnCopies Formalism.MainNotions.ModuliIntegralCharts.H1.PartialDerivativeExponent
variable {R : Type} [CommRing R] {d n : ℕ}

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.FormalGroupCopies.dofN_mem (F : Fin d → PS R 2 d) (T : Finset (Fin n)) {b : Fin n} (hb : b ∈ T)
    (u : Fin d → R) (g : PS R n d) (hg : g ∈ subV R (Vc d T)) :
    DofN F b u g ∈ subV R (Vc d T) := by sorry
