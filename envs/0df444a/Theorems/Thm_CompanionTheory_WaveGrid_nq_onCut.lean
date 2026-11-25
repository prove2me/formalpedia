-- Prove2me | Theorems.Thm_CompanionTheory_WaveGrid_nq_onCut
-- name    : CompanionTheory.WaveGrid.nq_onCut
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T06:25:12.529328+00:00
-- url     : https://prove2.me/theorems/78e5d669-6a92-5279-bb1b-4b8e1409cc90
-- title:
--   Wave Grid: nq on Cut
-- statement:
--   The Wave Grid construction uses the nq on Cut property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/BesselWaveGrids/NQText.lean#L130-L152
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/BesselWaveGrids/NQText.lean#L130-L152

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Interlace
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselWaveGrids_QwBound
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselWaveGrids_InterlacingGrids_PstMul
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselWaveGrids_NQText
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

theorem CompanionTheory.WaveGrid.nq_onCut (P : M.Par) (hOK : P.OK) (l : ℕ) (hl1 : 1 ≤ l) (hlk : l ≤ P.k) (hk : 2 ≤ P.k)
    (lam : ℕ → ℝ) (c g b : ℝ) (hL : LamData P lam c g b) (Y : ℝ) (hY : I.OnCut P.u P.u' l Y) :
    0 < (M.qC P (Y : ℂ)).re ∧
      GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid.Pst P.k P.r lam c Y * GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid.Pst P.k P.r lam c (Y + 1) ≤
        b ^ (8 * P.r + 20) / (P.T * P.T') * (M.qC P (Y : ℂ)).re := by sorry
