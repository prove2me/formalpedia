-- Prove2me | Theorems.Thm_CompanionTheory_WaveGrid_positioned_map_facW
-- name    : CompanionTheory.WaveGrid.positioned_map_facW
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:58:16.846561+00:00
-- url     : https://prove2.me/theorems/969d3b97-5c48-5320-974c-8f6661965113
-- title:
--   Wave Grid: positioned map fac W
-- statement:
--   The Wave Grid construction uses the positioned map fac W property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/BesselWaveGrids/QwBound.lean#L25-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/BesselWaveGrids/QwBound.lean#L25-L33

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

theorem CompanionTheory.WaveGrid.positioned_map_facW (w : List C.Letter) (y : ℝ) :
    (D.positionted w).map (fun l => facW l (y : ℂ)) = w.map fun l => ((fac l y : ℝ) : ℂ) := by sorry
