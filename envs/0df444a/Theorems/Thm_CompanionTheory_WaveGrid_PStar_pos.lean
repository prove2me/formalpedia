-- Prove2me | Theorems.Thm_CompanionTheory_WaveGrid_PStar_pos
-- name    : CompanionTheory.WaveGrid.PStar_pos
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T11:20:05.163041+00:00
-- url     : https://prove2.me/theorems/a84df79a-02b2-4fe5-8077-330cb806aef0
-- title:
--   Wave Grid: PStar pos
-- statement:
--   The Wave Grid construction uses the PStar pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/BesselWaveGrids/PStarTie.lean#L31-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/BesselWaveGrids/PStarTie.lean#L31-L32

import Definitions.Def_Formalism_HermitianCurvature_LetterProductDoubleDegreeCount
import Definitions.Def_Formalism_FormalDegreeBessel_StatementDS
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselWaveGrids_NqMovedExample
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselWaveGrids_PStarTie
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory CompanionTheory.WaveGrid
open Formalism.FourierDecayAlt Finset GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid

theorem CompanionTheory.WaveGrid.PStar_pos {n : ℕ} (lam : Fin n → ℝ) {c : ℝ} (hc : 0 < c) (y : ℝ) : 0 < PStar lam c y := by sorry
