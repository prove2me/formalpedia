-- Prove2me | Theorems.Thm_CompanionTheory_WaveGrid_qw_re_ge
-- name    : CompanionTheory.WaveGrid.qw_re_ge
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:56:34.512661+00:00
-- url     : https://prove2.me/theorems/a0a265b7-3549-408a-8bdc-1d84a63a6821
-- title:
--   Wave Grid: qw re ge
-- statement:
--   The Wave Grid construction uses the qw re ge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/BesselWaveGrids/QwBound.lean#L81-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/BesselWaveGrids/QwBound.lean#L81-L85

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

theorem CompanionTheory.WaveGrid.qw_re_ge (P : M.Par) (w : List C.Letter) (y : ℝ) (hq : 0 ≤ I.qpoly P.k P.T P.T' P.u P.u' y)
    (h : ∀ l ∈ w, 4 ≤ |y - l.2|) :
    (3 / 4 : ℝ) ^ w.length * I.qpoly P.k P.T P.T' P.u P.u' y ≤ (Wd.qw (M.qC P) (D.positionted w) (y : ℂ)).re := by sorry
