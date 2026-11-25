-- Prove2me | Theorems.Thm_CompanionTheory_WaveGrid_qw_indexed_ofReal
-- name    : CompanionTheory.WaveGrid.qw_indexed_ofReal
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:59:33.1672+00:00
-- url     : https://prove2.me/theorems/0af71fca-26d8-51d2-99e6-d4ce0dee0298
-- title:
--   Wave Grid: qw indexed of Real
-- statement:
--   The Wave Grid construction uses the qw indexed of Real property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/BesselWaveGrids/QwBound.lean#L45-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/BesselWaveGrids/QwBound.lean#L45-L50

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

theorem CompanionTheory.WaveGrid.qw_indexed_ofReal (P : M.Par) (w : List C.Letter) (y : ℝ) :
    Wd.qw (M.qC P) (D.positionted w) (y : ℂ) =
      ((I.qpoly P.k P.T P.T' P.u P.u' y * (w.map fun l => fac l y).prod : ℝ) : ℂ) := by sorry
