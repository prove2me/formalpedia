-- Prove2me | Theorems.Thm_CompanionTheory_WaveGrid_fac_ge
-- name    : CompanionTheory.WaveGrid.fac_ge
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:56:45.915918+00:00
-- url     : https://prove2.me/theorems/1d59b8da-fd6a-4715-893a-ec8f492e3ffc
-- title:
--   Wave Grid: fac ge
-- statement:
--   The Wave Grid construction uses the fac ge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/BesselWaveGrids/QwBound.lean#L52-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/BesselWaveGrids/QwBound.lean#L52-L68

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

theorem CompanionTheory.WaveGrid.fac_ge (l : C.Letter) (y : ℝ) (h : 4 ≤ |y - l.2|) : 3 / 4 ≤ fac l y := by sorry
