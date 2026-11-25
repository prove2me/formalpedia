-- Prove2me | Theorems.Thm_CompanionTheory_WaveGrid_Inhab_lamData_c
-- name    : CompanionTheory.WaveGrid.Inhab.lamData_c
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T07:15:10.976986+00:00
-- url     : https://prove2.me/theorems/5a37abd6-ee3c-5a43-a95e-0056d7a3209a
-- title:
--   Inhab: lam Data c
-- statement:
--   The Inhab construction uses the lam Data c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/BesselWaveGrids/NqOfLamData.lean#L241-L248
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/BesselWaveGrids/NqOfLamData.lean#L241-L248

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

theorem CompanionTheory.WaveGrid.Inhab.lamData_c : LamData Pc cfg₁.lam 10 (4 * cfg₁.Del) 401 := by sorry
