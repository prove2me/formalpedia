-- Prove2me | Theorems.Thm_CompanionTheory_WaveGrid_nq_onCut_neg_thirty
-- name    : CompanionTheory.WaveGrid.nq_onCut_neg_thirty
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T11:18:49.263447+00:00
-- url     : https://prove2.me/theorems/19c1511b-d5e7-5485-a0dd-8876e045b1c2
-- title:
--   Wave Grid: nq on Cut neg thirty
-- statement:
--   The Wave Grid construction uses the nq on Cut neg thirty property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/BesselWaveGrids/NQText.lean#L154-L160
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/BesselWaveGrids/NQText.lean#L154-L160

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

theorem CompanionTheory.WaveGrid.nq_onCut_neg_thirty :
    0 < (M.qC P₀ ((-30 : ℝ) : ℂ)).re ∧
      GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid.Pst P₀.k P₀.r lam₀ 1 (-30) *
          GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid.Pst P₀.k P₀.r lam₀ 1 (-30 + 1) ≤
        40 ^ (8 * P₀.r + 20) / (P₀.T * P₀.T') * (M.qC P₀ ((-30 : ℝ) : ℂ)).re := by sorry
