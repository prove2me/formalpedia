-- Prove2me | Theorems.Thm_CompanionTheory_WaveGrid_LamData_toPair
-- name    : CompanionTheory.WaveGrid.LamData.toPair
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T06:44:07.754878+00:00
-- url     : https://prove2.me/theorems/fb6001ab-9d98-5eff-8501-2852870fa791
-- title:
--   Lam Data: to Pair
-- statement:
--   The Lam Data construction uses the to Pair property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/BesselWaveGrids/NqMovedExample.lean#L18-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/BesselWaveGrids/NqMovedExample.lean#L18-L30

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

theorem CompanionTheory.WaveGrid.LamData.toPair {P : M.Par} {lam : ℕ → ℝ} {c g b : ℝ} (hL : LamData P lam c g b) {l : ℕ} (hl1 : 1 ≤ l)
    (hlk : l ≤ P.k) : PairData P l lam c g b := by sorry
