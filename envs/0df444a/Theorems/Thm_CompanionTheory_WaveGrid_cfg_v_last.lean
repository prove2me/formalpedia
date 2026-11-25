-- Prove2me | Theorems.Thm_CompanionTheory_WaveGrid_cfg_v_last
-- name    : CompanionTheory.WaveGrid.cfg_v_last
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T07:15:36.586798+00:00
-- url     : https://prove2.me/theorems/b5e0bd2d-70e2-4950-82de-ac0b4dfb71a6
-- title:
--   Wave Grid: cfg v last
-- statement:
--   The Wave Grid construction uses the cfg v last property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/BesselWaveGrids/CfgTie.lean#L28-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/BesselWaveGrids/CfgTie.lean#L28-L30

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

theorem CompanionTheory.WaveGrid.cfg_v_last (hk : 1 ≤ c.k) : c.v (c.k - 1) = c.vlast := by sorry
