-- Prove2me | Theorems.Thm_CompanionTheory_WaveGrid_Inhab_ex_cfg
-- name    : CompanionTheory.WaveGrid.Inhab.ex_cfg
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T11:19:30.028661+00:00
-- url     : https://prove2.me/theorems/b2e5cbd4-0dd9-4df3-9b00-86b45e73f47c
-- title:
--   Inhab: ex cfg
-- statement:
--   The Inhab construction uses the ex cfg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/BesselWaveGrids/NqOfLamData.lean#L274-L282
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/BesselWaveGrids/NqOfLamData.lean#L274-L282

import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselWaveGrids_PStarTie
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselWaveGrids_CfgTie
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselWaveGrids_NqOfLamData
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory CompanionTheory.WaveGrid CompanionTheory.WaveGrid.Inhab
open Formalism.FourierDecayAlt Finset CompanionTheory.WaveGrid GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid

theorem CompanionTheory.WaveGrid.Inhab.ex_cfg : NQ Pc (PStar (fun s : Fin (2 * Pc.r + Pc.k + 1) => cfg₁.lam (s + 1)) 10) {-107, -112, -117}
    (nqΛ Pc 401) := by sorry
