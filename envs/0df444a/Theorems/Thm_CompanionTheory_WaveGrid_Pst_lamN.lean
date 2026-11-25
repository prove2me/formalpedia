-- Prove2me | Theorems.Thm_CompanionTheory_WaveGrid_Pst_lamN
-- name    : CompanionTheory.WaveGrid.Pst_lamN
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T07:01:27.864511+00:00
-- url     : https://prove2.me/theorems/0ec7ca8c-1fa6-463e-8fdb-eb201116f7ad
-- title:
--   Wave Grid: Pst lam N
-- statement:
--   The Wave Grid construction uses the Pst lam N property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/BesselWaveGrids/PStarTie.lean#L19-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/BesselWaveGrids/PStarTie.lean#L19-L29

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

theorem CompanionTheory.WaveGrid.Pst_lamN (k r : ℕ) (lam : Fin (2 * r + k + 1) → ℝ) (c y : ℝ) : Pst k r (lamN lam) c y = PStar lam c y := by sorry
