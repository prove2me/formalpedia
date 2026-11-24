-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_CIndBCNab_map_eval_first_point_zero
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.CIndBCNab.map_eval_first_point_zero
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T09:57:47.057905+00:00
-- url     : https://prove2.me/theorems/29dec906-406c-4bdc-acda-412a098a58ee
-- title:
--   CInd BCNab: map eval first point zero
-- statement:
--   The CInd BCNab construction uses the map eval first point zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/CIndBCNab.lean#L46-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/CIndBCNab.lean#L46-L54

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

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.CIndBCNab.map_eval_first_point_zero (g : PS S 2 d) :
    map ψ (ev (n := 1) ![pt S d 0, 0] g) = ev (n := 1) ![pt S' d 0, 0] (map ψ g) := by sorry
