-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_CIndBCNab_map_DmonOf
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.CIndBCNab.map_DmonOf
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T09:57:40.368368+00:00
-- url     : https://prove2.me/theorems/6bf2db4f-f118-46f9-8158-45abd3b9f018
-- title:
--   CInd BCNab: map Dmon Of
-- statement:
--   The CInd BCNab construction uses the map Dmon Of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/CIndBCNab.lean#L66-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/CIndBCNab.lean#L66-L72

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

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.CIndBCNab.map_DmonOf (F : Fin d → PS S 2 d) {κ : Type} [Fintype κ] (u : κ → Fin d → S) (e : κ →₀ ℕ)
    (f : PS S 1 d) :
    map ψ (DmonOf F u e f) = DmonOf (fun j => map ψ (F j)) (fun l i => ψ (u l i)) e (map ψ f) := by sorry
