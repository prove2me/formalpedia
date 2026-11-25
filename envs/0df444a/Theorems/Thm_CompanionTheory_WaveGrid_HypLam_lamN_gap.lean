-- Prove2me | Theorems.Thm_CompanionTheory_WaveGrid_HypLam_lamN_gap
-- name    : CompanionTheory.WaveGrid.HypLam.lamN_gap
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T07:08:22.608138+00:00
-- url     : https://prove2.me/theorems/28a70bdf-f10b-48ba-93ff-412ee7a35a08
-- title:
--   Hyp Lam: lam N gap
-- statement:
--   The Hyp Lam construction uses the lam N gap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/BesselWaveGrids/PStarTie.lean#L91-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/BesselWaveGrids/PStarTie.lean#L91-L97

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

theorem CompanionTheory.WaveGrid.HypLam.lamN_gap (h : HypLam P.k P.r lam c g b) :
    ∀ s, 1 ≤ s → s + 1 ≤ P.k - 1 → lamN lam (s + 1) + g ≤ lamN lam s := by sorry
