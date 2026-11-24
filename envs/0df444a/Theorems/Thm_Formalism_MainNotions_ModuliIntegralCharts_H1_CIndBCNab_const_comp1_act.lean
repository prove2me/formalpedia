-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_CIndBCNab_const_comp1_act
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.CIndBCNab.const_comp1_act
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T09:57:33.396028+00:00
-- url     : https://prove2.me/theorems/323cc68d-9b16-46c1-98ec-b151a22ca9d3
-- title:
--   CInd BCNab: const comp1 act
-- statement:
--   The CInd BCNab construction uses the const comp1 act property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/CIndBCNab.lean#L97-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/CIndBCNab.lean#L97-L105

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndBC
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndBCNab
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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.CIndBCNab
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {S S' : Type} [CommRing S] [CommRing S'] (ψ : S →+* S') {d : ℕ}
variable [Algebra ℚ S] [Algebra ℚ S']
variable {O : Type} [CommRing O] [StarRing O]

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.CIndBCNab.const_comp1_act (B : FB S d O) (a : O) (i : Fin d) :
    constantCoeff (comp1 (B.actK S a) (pt S (n := 1) d 0) i) = 0 := by sorry
