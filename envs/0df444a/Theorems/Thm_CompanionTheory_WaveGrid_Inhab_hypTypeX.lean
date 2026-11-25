-- Prove2me | Theorems.Thm_CompanionTheory_WaveGrid_Inhab_hypTypeX
-- name    : CompanionTheory.WaveGrid.Inhab.hypTypeX
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T07:08:38.798988+00:00
-- url     : https://prove2.me/theorems/e4320088-629e-4933-9e4a-930e4cf2f8c9
-- title:
--   Inhab: hyp Type X
-- statement:
--   The Inhab construction uses the hyp Type X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/BesselWaveGrids/NqOfLamData.lean#L181-L197
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/BesselWaveGrids/NqOfLamData.lean#L181-L197

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

theorem CompanionTheory.WaveGrid.Inhab.hypTypeX (x : ℤ) (hx : 0 ≤ x) (hx' : x ≤ 79) : HypType 3 0 (lamX x) uX 80 := by sorry
