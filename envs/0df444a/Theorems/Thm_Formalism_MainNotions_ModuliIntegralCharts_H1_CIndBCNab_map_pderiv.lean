-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_CIndBCNab_map_pderiv
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.CIndBCNab.map_pderiv
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T09:57:38.386379+00:00
-- url     : https://prove2.me/theorems/8745d1bb-9f68-4a0b-b92f-fdd0f60fd29b
-- title:
--   CInd BCNab: map pderiv
-- statement:
--   The CInd BCNab construction uses the map pderiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/CIndBCNab.lean#L36-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/CIndBCNab.lean#L36-L39

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

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.CIndBCNab.map_pderiv {σ : Type} (i : σ) (f : MvPowerSeries σ S) :
    map ψ (pderiv S i f) = pderiv S' i (map ψ f) := by sorry
