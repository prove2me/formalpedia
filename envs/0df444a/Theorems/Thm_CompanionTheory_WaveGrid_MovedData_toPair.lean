-- Prove2me | Theorems.Thm_CompanionTheory_WaveGrid_MovedData_toPair
-- name    : CompanionTheory.WaveGrid.MovedData.toPair
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T06:40:20.862685+00:00
-- url     : https://prove2.me/theorems/bdc18793-a995-5c52-b2cc-92c323c5eeed
-- title:
--   Moved Data: to Pair
-- statement:
--   The Moved Data construction uses the to Pair property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/BesselWaveGrids/NqMovedExample.lean#L68-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/BesselWaveGrids/NqMovedExample.lean#L68-L83

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

theorem CompanionTheory.WaveGrid.MovedData.toPair {P : M.Par} {l : ℕ} {lam : ℕ → ℝ} {c g b : ℝ} (hM : MovedData P l lam c g b) :
    PairData P l lam c g b := by sorry
