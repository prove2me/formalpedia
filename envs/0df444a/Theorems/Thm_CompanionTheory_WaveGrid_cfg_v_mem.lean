-- Prove2me | Theorems.Thm_CompanionTheory_WaveGrid_cfg_v_mem
-- name    : CompanionTheory.WaveGrid.cfg_v_mem
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T07:12:03.500817+00:00
-- url     : https://prove2.me/theorems/98199ba0-df82-54d5-bd64-5048415d15ee
-- title:
--   Wave Grid: cfg v mem
-- statement:
--   The Wave Grid construction uses the cfg v mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/BesselWaveGrids/CfgTie.lean#L19-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/BesselWaveGrids/CfgTie.lean#L19-L26

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselWaveGrids_NqMovedExample
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselWaveGrids_CfgTie
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory CompanionTheory.WaveGrid
open Formalism.FourierDecayAlt Finset
variable (c : Sz.Cfg)

theorem CompanionTheory.WaveGrid.cfg_v_mem (hok : c.Ok) (i : ℕ) (hi1 : 1 ≤ i) (hi : i + 1 ≤ c.k) : c.vlast ≤ c.v i ∧ c.v i ≤ c.v 1 := by sorry
