-- Prove2me | Theorems.Thm_CompanionTheory_WaveGrid_prod_fac_ge
-- name    : CompanionTheory.WaveGrid.prod_fac_ge
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:59:27.446855+00:00
-- url     : https://prove2.me/theorems/e3d011c5-d099-5373-aa54-f8368dfad25b
-- title:
--   Wave Grid: prod fac ge
-- statement:
--   The Wave Grid construction uses the prod fac ge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/BesselWaveGrids/QwBound.lean#L70-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/BesselWaveGrids/QwBound.lean#L70-L79

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

theorem CompanionTheory.WaveGrid.prod_fac_ge (w : List C.Letter) (y : ℝ) (h : ∀ l ∈ w, 4 ≤ |y - l.2|) :
    (3 / 4 : ℝ) ^ w.length ≤ (w.map fun l => fac l y).prod := by sorry
