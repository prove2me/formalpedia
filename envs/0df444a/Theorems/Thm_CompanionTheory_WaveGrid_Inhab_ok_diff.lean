-- Prove2me | Theorems.Thm_CompanionTheory_WaveGrid_Inhab_ok_diff
-- name    : CompanionTheory.WaveGrid.Inhab.ok_diff
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T11:19:54.424936+00:00
-- url     : https://prove2.me/theorems/f98a0222-6960-4006-9d3c-4c8eaa922e65
-- title:
--   Inhab: ok diff
-- statement:
--   The Inhab construction uses the ok diff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/BesselWaveGrids/NqOfLamData.lean#L18-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/BesselWaveGrids/NqOfLamData.lean#L18-L29

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

theorem CompanionTheory.WaveGrid.Inhab.ok_diff (P : M.Par) (hk : 1 ≤ P.k) (hT : 0 < P.T) (hT' : 0 < P.T') (lam : Fin (2 * P.r + P.k + 1) → ℝ)
    (b : ℝ) (hc : Formalism.QuantumDeterminants.IsHCParam lam) (hu : HypType P.k P.r lam P.u b) (hu' : HypType P.k P.r lam P.u' b) :
    P.OK := by sorry
