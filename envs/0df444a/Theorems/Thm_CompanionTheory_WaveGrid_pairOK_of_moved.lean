-- Prove2me | Theorems.Thm_CompanionTheory_WaveGrid_pairOK_of_moved
-- name    : CompanionTheory.WaveGrid.pairOK_of_moved
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T07:14:50.134838+00:00
-- url     : https://prove2.me/theorems/f3605a17-e531-457b-8138-66151dbbd2e4
-- title:
--   Wave Grid: pair OK of moved
-- statement:
--   The Wave Grid construction uses the pair OK of moved property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/BesselWaveGrids/NqMovedExample.lean#L32-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/BesselWaveGrids/NqMovedExample.lean#L32-L54

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

theorem CompanionTheory.WaveGrid.pairOK_of_moved (k l : ℕ) (lam u v : ℕ → ℝ) (x : ℝ)
    (h : ∀ s, 1 ≤ s → s ≤ k - 1 → lam s + 1 / 2 ≤ u s ∧ u (s + 1) ≤ lam s - 1 / 2)
    (hv : ∀ i, i ≠ l → v i = u i) (hx : (u l < x ∧ x < v l) ∨ (v l < x ∧ x < u l)) :
    ∃ e, PairOK k lam v e x := by sorry
