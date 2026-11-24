-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpTieAlg_pderiv_cpy
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.ExpTieAlg.pderiv_cpy
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T10:08:05.765841+00:00
-- url     : https://prove2.me/theorems/1c2d3907-13bd-4467-a5d5-b5567f0f8dff
-- title:
--   Exp Tie Alg: pderiv cpy
-- statement:
--   The Exp Tie Alg construction uses the pderiv cpy property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ExpTieAlg.lean#L191-L200
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ExpTieAlg.lean#L191-L200

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

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.ExpTieAlg.pderiv_cpy (b : Fin 2) (q : Fin N) (g : MvPowerSeries (Fin 1 × Fin N) S) :
    pderiv S ((1 : Fin 2), q) (subst (cpy (S := S) b) g) =
      if b = 1 then subst (cpy (S := S) b) (pderiv S ((0 : Fin 1), q) g) else 0 := by sorry
