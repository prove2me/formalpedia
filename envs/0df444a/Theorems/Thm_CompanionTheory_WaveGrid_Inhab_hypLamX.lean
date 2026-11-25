-- Prove2me | Theorems.Thm_CompanionTheory_WaveGrid_Inhab_hypLamX
-- name    : CompanionTheory.WaveGrid.Inhab.hypLamX
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T07:31:11.615708+00:00
-- url     : https://prove2.me/theorems/8720bdc7-cb65-5d47-9d35-1da94dd7c76c
-- title:
--   Inhab: hyp Lam X
-- statement:
--   The Inhab construction uses the hyp Lam X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/BesselWaveGrids/NqOfLamData.lean#L162-L179
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/BesselWaveGrids/NqOfLamData.lean#L162-L179

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

theorem CompanionTheory.WaveGrid.Inhab.hypLamX (x : ℤ) (hx : 0 ≤ x) (hx' : x ≤ 79) : HypLam 3 0 (lamX x) 10 20 80 := by sorry
