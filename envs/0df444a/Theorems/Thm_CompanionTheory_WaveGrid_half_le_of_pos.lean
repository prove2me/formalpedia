-- Prove2me | Theorems.Thm_CompanionTheory_WaveGrid_half_le_of_pos
-- name    : CompanionTheory.WaveGrid.half_le_of_pos
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T07:15:34.836067+00:00
-- url     : https://prove2.me/theorems/03716b55-3a87-5b8a-80ae-6d33b7c378e3
-- title:
--   Wave Grid: half le of pos
-- statement:
--   The Wave Grid construction uses the half le of pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/BesselWaveGrids/PStarTie.lean#L49-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/BesselWaveGrids/PStarTie.lean#L49-L55

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

theorem CompanionTheory.WaveGrid.half_le_of_pos {x : ℝ} (m : ℤ) (hx : x = m + 1 / 2) (h : 0 < x) : 1 / 2 ≤ x := by sorry
