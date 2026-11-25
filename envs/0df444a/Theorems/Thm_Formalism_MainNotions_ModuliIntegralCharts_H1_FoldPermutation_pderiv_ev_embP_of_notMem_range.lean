-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_FoldPermutation_pderiv_ev_embP_of_notMem_range
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.FoldPermutation.pderiv_ev_embP_of_notMem_range
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T01:59:14.146889+00:00
-- url     : https://prove2.me/theorems/e2de999f-1a71-4cb3-8e36-a5bf2812fec8
-- title:
--   Fold Permutation: pderiv ev emb P of not Mem range
-- statement:
--   The Fold Permutation construction uses the pderiv ev emb P of not Mem range property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/FoldPermutation.lean#L47-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/FoldPermutation.lean#L47-L53

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FormalGroupCopies
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_DofComm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeTrans
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FoldPermutation
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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.FoldPermutation
open MvPowerSeries Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
open Formalism.MainNotions.ModuliIntegralCharts.H1.FormalGroupOnCopies Formalism.MainNotions.ModuliIntegralCharts.H1.PartialDerivativeExponent Formalism.MainNotions.ModuliIntegralCharts.H1.FormalGroupCopies
variable {k : Type} [CommRing k] {d : ℕ}

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.FoldPermutation.pderiv_ev_embP_of_notMem_range {n' n : ℕ} (e : Fin n' → Fin n) (g : PS k n' d) (c : Fin n) (hc : ∀ b, e b ≠ c)
    (j : Fin d) : pderiv k (c, j) (ev (embP e) g) = 0 := by sorry
