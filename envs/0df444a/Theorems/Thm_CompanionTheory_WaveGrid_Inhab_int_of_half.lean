-- Prove2me | Theorems.Thm_CompanionTheory_WaveGrid_Inhab_int_of_half
-- name    : CompanionTheory.WaveGrid.Inhab.int_of_half
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T07:07:57.972376+00:00
-- url     : https://prove2.me/theorems/7e9fc2ed-f42c-49e4-96e9-4d17c82e819e
-- title:
--   Inhab: int of half
-- statement:
--   The Inhab construction uses the int of half property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/BesselWaveGrids/NqOfLamData.lean#L8-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/BesselWaveGrids/NqOfLamData.lean#L8-L16

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

theorem CompanionTheory.WaveGrid.Inhab.int_of_half {k : ℕ} {u v : ℕ → ℝ} (hk : 1 ≤ k)
    (hu : ∀ i, 1 ≤ i → i ≤ k → ∃ m : ℤ, u i - ((k : ℝ) - 1) / 2 = m)
    (hv : ∀ i, 1 ≤ i → i ≤ k → ∃ m : ℤ, v i - ((k : ℝ) - 1) / 2 = m) :
    ∀ i ∈ Icc 1 k, ∃ n : ℤ, v i - u 1 = n := by sorry
