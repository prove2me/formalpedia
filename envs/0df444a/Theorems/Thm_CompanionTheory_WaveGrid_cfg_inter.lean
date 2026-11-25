-- Prove2me | Theorems.Thm_CompanionTheory_WaveGrid_cfg_inter
-- name    : CompanionTheory.WaveGrid.cfg_inter
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T07:27:58.847796+00:00
-- url     : https://prove2.me/theorems/6ef6b44d-46e0-59ca-a37e-1f222c07efee
-- title:
--   Wave Grid: cfg inter
-- statement:
--   The Wave Grid construction uses the cfg inter property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/BesselWaveGrids/CfgTie.lean#L42-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/BesselWaveGrids/CfgTie.lean#L42-L76

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

theorem CompanionTheory.WaveGrid.cfg_inter (hok : c.Ok) (de : ℕ → ℝ) (hde : ∀ i, de i = 0 ∨ de i = 1) (s : ℕ) (hs1 : 1 ≤ s)
    (hsk : s ≤ c.k - 1) : c.lam s + 1 / 2 ≤ c.u de s ∧ c.u de (s + 1) ≤ c.lam s - 1 / 2 := by sorry
