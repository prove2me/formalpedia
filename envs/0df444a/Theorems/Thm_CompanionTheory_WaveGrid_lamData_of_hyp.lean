-- Prove2me | Theorems.Thm_CompanionTheory_WaveGrid_lamData_of_hyp
-- name    : CompanionTheory.WaveGrid.lamData_of_hyp
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T11:20:48.220819+00:00
-- url     : https://prove2.me/theorems/1e3dd68d-96f7-4a87-b9fb-baac2365868e
-- title:
--   Wave Grid: lam Data of hyp
-- statement:
--   The Wave Grid construction uses the lam Data of hyp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/BesselWaveGrids/PStarTie.lean#L99-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/BesselWaveGrids/PStarTie.lean#L99-L109

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
variable {P : M.Par} {lam : Fin (2 * P.r + P.k + 1) → ℝ} {c g b : ℝ}

theorem CompanionTheory.WaveGrid.lamData_of_hyp (h : HypLam P.k P.r lam c g b) (hu : HypType P.k P.r lam P.u b)
    (hu' : HypType P.k P.r lam P.u' b) : LamData P (lamN lam) c g b := by sorry
