-- Prove2me | Theorems.Thm_CompanionTheory_WaveGrid_nq_moved_example
-- name    : CompanionTheory.WaveGrid.nq_moved_example
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T11:18:44.457983+00:00
-- url     : https://prove2.me/theorems/189a27ad-8bb8-56cf-af07-c564815ff6bd
-- title:
--   Wave Grid: nq moved example
-- statement:
--   The Wave Grid construction uses the nq moved example property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/BesselWaveGrids/NqMovedExample.lean#L170-L175
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/BesselWaveGrids/NqMovedExample.lean#L170-L175

import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselWaveGrids_NQText
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselWaveGrids_NqMovedExample
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory CompanionTheory.WaveGrid
open Formalism.FourierDecayAlt Finset GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid

theorem CompanionTheory.WaveGrid.nq_moved_example :
    0 < (M.qC P₁ ((-10 : ℝ) : ℂ)).re ∧
      Pst P₁.k P₁.r lam₀ 1 (-10) * Pst P₁.k P₁.r lam₀ 1 (-10 + 1) ≤
        40 ^ (8 * P₁.r + 20) / (P₁.T * P₁.T') * (M.qC P₁ ((-10 : ℝ) : ℂ)).re := by sorry
