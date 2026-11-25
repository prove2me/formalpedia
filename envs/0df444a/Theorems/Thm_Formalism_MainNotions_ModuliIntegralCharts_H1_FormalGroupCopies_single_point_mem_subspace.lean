-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_FormalGroupCopies_single_point_mem_subspace
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.FormalGroupCopies.single_point_mem_subspace
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T01:11:02.58743+00:00
-- url     : https://prove2.me/theorems/304672a7-e144-4342-bbe9-21f222e41504
-- title:
--   Formal Group Copies: single point mem subspace
-- statement:
--   The Formal Group Copies construction uses the single point mem subspace property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/FormalGroupCopies.lean#L65-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/FormalGroupCopies.lean#L65-L79

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

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.FormalGroupCopies.single_point_mem_subspace (T : Finset (Fin n)) (b : Fin n) (hb : b ∈ T) :
    ∀ (q : Fin 1) (i : Fin d), (![pt R d b] : Fin 1 → Pt R n d) q i ∈ subV R (Vc d T) := by sorry
