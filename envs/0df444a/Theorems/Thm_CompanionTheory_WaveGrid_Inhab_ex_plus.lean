-- Prove2me | Theorems.Thm_CompanionTheory_WaveGrid_Inhab_ex_plus
-- name    : CompanionTheory.WaveGrid.Inhab.ex_plus
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T11:18:37.19192+00:00
-- url     : https://prove2.me/theorems/0745897c-f048-5703-9734-42faec23ac37
-- title:
--   Inhab: ex plus
-- statement:
--   The Inhab construction uses the ex plus property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/BesselWaveGrids/NqOfLamData.lean#L199-L205
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/BesselWaveGrids/NqOfLamData.lean#L199-L205

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

theorem CompanionTheory.WaveGrid.Inhab.ex_plus : NQ ⟨3, 0, 1, 1, uX, uP uX 1 36⟩ (PStar (lamX 20) 10) {-3, -20, -21, -34}
    (nqΛ ⟨3, 0, 1, 1, uX, uP uX 1 36⟩ 80) := by sorry
