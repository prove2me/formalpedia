-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpTieAlg_subst_sz_cpy
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.ExpTieAlg.subst_sz_cpy
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T10:00:47.151727+00:00
-- url     : https://prove2.me/theorems/c24fb4cb-ade8-404d-b442-2a1c6ea03136
-- title:
--   Exp Tie Alg: subst sz cpy
-- statement:
--   The Exp Tie Alg construction uses the subst sz cpy property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ExpTieAlg.lean#L166-L189
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ExpTieAlg.lean#L166-L189

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
variable (F : Fin d → PS S 2 d) (φ : Fin d → MvPowerSeries (Fin 1 × Fin N) S)

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.ExpTieAlg.subst_sz_cpy (b : Fin 2) (g : MvPowerSeries (Fin 1 × Fin N) S) :
    subst (sz (S := S) (N := N)) (subst (cpy (S := S) b) g) = if b = 0 then g else C (constantCoeff g) := by sorry
