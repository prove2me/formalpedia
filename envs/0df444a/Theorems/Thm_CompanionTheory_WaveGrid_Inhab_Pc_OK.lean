-- Prove2me | Theorems.Thm_CompanionTheory_WaveGrid_Inhab_Pc_OK
-- name    : CompanionTheory.WaveGrid.Inhab.Pc_OK
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T07:15:21.170885+00:00
-- url     : https://prove2.me/theorems/77ef8e74-3210-5009-a297-3ef3cc6b8d64
-- title:
--   Inhab: Pc OK
-- statement:
--   The Inhab construction uses the Pc OK property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/BesselWaveGrids/NqOfLamData.lean#L250-L272
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/BesselWaveGrids/NqOfLamData.lean#L250-L272

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

theorem CompanionTheory.WaveGrid.Inhab.Pc_OK : Pc.OK := by sorry
