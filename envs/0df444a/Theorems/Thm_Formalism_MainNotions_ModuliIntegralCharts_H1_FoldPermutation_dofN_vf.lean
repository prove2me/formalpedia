-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_FoldPermutation_dofN_vf
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.FoldPermutation.dofN_vf
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T01:52:50.934056+00:00
-- url     : https://prove2.me/theorems/a67edfb4-38d5-4657-a955-b37721404098
-- title:
--   Fold Permutation: dof N vf
-- statement:
--   The Fold Permutation construction uses the dof N vf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/FoldPermutation.lean#L83-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/FoldPermutation.lean#L83-L99

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

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.FoldPermutation.dofN_vf (G : FGLaw k d) {n : ℕ} (b : Fin n) (u : Fin d → k) (g : PS k n d) :
    DofN G.F b u g = WickVanishing.Nab.vf (cB G b u) g := by sorry
