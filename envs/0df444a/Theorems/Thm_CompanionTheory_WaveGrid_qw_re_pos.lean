-- Prove2me | Theorems.Thm_CompanionTheory_WaveGrid_qw_re_pos
-- name    : CompanionTheory.WaveGrid.qw_re_pos
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T11:25:47.600986+00:00
-- url     : https://prove2.me/theorems/d8bdb3ea-edb1-4706-b998-20acf56a9045
-- title:
--   Wave Grid: qw re pos
-- statement:
--   The Wave Grid construction uses the qw re pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/BesselWaveGrids/QwBound.lean#L87-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/BesselWaveGrids/QwBound.lean#L87-L89

import Definitions.Def_Formalism_HermitianCurvature_StatementD
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselWaveGrids_QwBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory CompanionTheory.WaveGrid
open Formalism.FourierDecayAlt

theorem CompanionTheory.WaveGrid.qw_re_pos (P : M.Par) (w : List C.Letter) (y : ℝ) (hq : 0 < I.qpoly P.k P.T P.T' P.u P.u' y)
    (h : ∀ l ∈ w, 4 ≤ |y - l.2|) : 0 < (Wd.qw (M.qC P) (D.positionted w) (y : ℂ)).re := by sorry
