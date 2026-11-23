-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_CIndBCNab_const_pair
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.CIndBCNab.const_pair
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T13:24:52.820626+00:00
-- url     : https://prove2.me/theorems/11383155-30ed-409d-b010-a6282cb3eaa6
-- title:
--   CInd BCNab: const pair
-- statement:
--   The CInd BCNab construction uses the const pair property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/CIndBCNab.lean#L107-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/CIndBCNab.lean#L107-L112

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

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.CIndBCNab.const_pair (B : FB S d O) (w0 : O) :
    ∀ j i, constantCoeff ((![pt S d 0, comp1 (B.actK S w0) (pt S d 0)] : Fin 2 → Pt S 1 d) j i) = 0 := by sorry
