-- Prove2me | Theorems.Thm_CompanionTheory_WaveGrid_Inhab_nq_of_lamData
-- name    : CompanionTheory.WaveGrid.Inhab.nq_of_lamData
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T07:43:18.068827+00:00
-- url     : https://prove2.me/theorems/80f61ffe-f99b-491e-aa4a-eb1c51bcc4c3
-- title:
--   Inhab: nq of lam Data
-- statement:
--   The Inhab construction uses the nq of lam Data property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/BesselWaveGrids/NqOfLamData.lean#L215-L232
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/BesselWaveGrids/NqOfLamData.lean#L215-L232

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

theorem CompanionTheory.WaveGrid.Inhab.nq_of_lamData (P : M.Par) (hOK : P.OK) (l : ℕ) (hl1 : 1 ≤ l) (hlk : l ≤ P.k) (hk : 2 ≤ P.k) (lam : ℕ → ℝ)
    (c g b : ℝ) (hL : LamData P lam c g b) (Y : Finset ℝ) (hY : ∀ y ∈ Y, I.OnCut P.u P.u' l y) :
    NQ P (PStar (fun s : Fin (2 * P.r + P.k + 1) => lam (s + 1)) c) Y (nqΛ P b) := by sorry
