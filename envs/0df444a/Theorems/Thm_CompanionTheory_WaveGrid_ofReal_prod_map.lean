-- Prove2me | Theorems.Thm_CompanionTheory_WaveGrid_ofReal_prod_map
-- name    : CompanionTheory.WaveGrid.ofReal_prod_map
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:58:11.110283+00:00
-- url     : https://prove2.me/theorems/e08a6587-8ca5-50ab-a158-b66b00dd0900
-- title:
--   Wave Grid: of Real prod map
-- statement:
--   The Wave Grid construction uses the of Real prod map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/BesselWaveGrids/QwBound.lean#L35-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/BesselWaveGrids/QwBound.lean#L35-L39

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

theorem CompanionTheory.WaveGrid.ofReal_prod_map (w : List C.Letter) (f : C.Letter → ℝ) :
    (((w.map f).prod : ℝ) : ℂ) = (w.map fun l => ((f l : ℝ) : ℂ)).prod := by sorry
