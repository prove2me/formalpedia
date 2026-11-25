-- Prove2me | Theorems.Thm_CompanionTheory_WaveGrid_cfg_u_le
-- name    : CompanionTheory.WaveGrid.cfg_u_le
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T07:13:52.1827+00:00
-- url     : https://prove2.me/theorems/def0aa59-bea8-40d4-98c7-243e66112f15
-- title:
--   Wave Grid: cfg u le
-- statement:
--   The Wave Grid construction uses the cfg u le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/BesselWaveGrids/CfgTie.lean#L78-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/BesselWaveGrids/CfgTie.lean#L78-L98

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

theorem CompanionTheory.WaveGrid.cfg_u_le (hok : c.Ok) (de : ℕ → ℝ) (hde : ∀ i, de i = 0 ∨ de i = 1) (b : ℝ) (ha : c.a ≤ b)
    (hb1 : c.b 1 ≤ b) (i : ℕ) (hi1 : 1 ≤ i) (hik : i ≤ c.k) : |c.u de i| ≤ b := by sorry
