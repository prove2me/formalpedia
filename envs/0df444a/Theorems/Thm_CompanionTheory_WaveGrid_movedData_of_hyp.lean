-- Prove2me | Theorems.Thm_CompanionTheory_WaveGrid_movedData_of_hyp
-- name    : CompanionTheory.WaveGrid.movedData_of_hyp
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T07:28:55.202398+00:00
-- url     : https://prove2.me/theorems/a02597ef-8b9f-4c51-96af-74b34ad2ecf7
-- title:
--   Wave Grid: moved Data of hyp
-- statement:
--   The Wave Grid construction uses the moved Data of hyp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/BesselWaveGrids/PStarTie.lean#L111-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/BesselWaveGrids/PStarTie.lean#L111-L122

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

theorem CompanionTheory.WaveGrid.movedData_of_hyp (h : HypLam P.k P.r lam c g b) (hu : HypType P.k P.r lam P.u b) {l : ℕ} (hl1 : 1 ≤ l)
    (hlk : l ≤ P.k) (hmv : ∀ i, i ≠ l → P.u' i = P.u i) (hl : |P.u' l| ≤ b) : MovedData P l (lamN lam) c g b := by sorry
