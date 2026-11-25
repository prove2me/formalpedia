-- Prove2me | Theorems.Thm_CompanionTheory_WaveGrid_nq_onCut_pair
-- name    : CompanionTheory.WaveGrid.nq_onCut_pair
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T06:42:05.100004+00:00
-- url     : https://prove2.me/theorems/fe48fc88-ca00-5c8d-966a-124e48f28ce4
-- title:
--   Wave Grid: nq on Cut pair
-- statement:
--   The Wave Grid construction uses the nq on Cut pair property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/BesselWaveGrids/NqMovedExample.lean#L85-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/BesselWaveGrids/NqMovedExample.lean#L85-L106

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

theorem CompanionTheory.WaveGrid.nq_onCut_pair (P : M.Par) (hOK : P.OK) (l : ℕ) (hl1 : 1 ≤ l) (hlk : l ≤ P.k) (hk : 2 ≤ P.k)
    (lam : ℕ → ℝ) (c g b : ℝ) (hL : PairData P l lam c g b) (Y : ℝ) (hY : I.OnCut P.u P.u' l Y) :
    0 < (M.qC P (Y : ℂ)).re ∧
      Pst P.k P.r lam c Y * Pst P.k P.r lam c (Y + 1) ≤
        b ^ (8 * P.r + 20) / (P.T * P.T') * (M.qC P (Y : ℂ)).re := by sorry
