-- Prove2me | Theorems.Thm_CompanionTheory_WaveGrid_HypLam_lamN_le
-- name    : CompanionTheory.WaveGrid.HypLam.lamN_le
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T07:00:27.891618+00:00
-- url     : https://prove2.me/theorems/2286f0a5-5601-4c8b-b934-c0690f0c5d0c
-- title:
--   Hyp Lam: lam N le
-- statement:
--   The Hyp Lam construction uses the lam N le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/BesselWaveGrids/PStarTie.lean#L84-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/BesselWaveGrids/PStarTie.lean#L84-L89

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

theorem CompanionTheory.WaveGrid.HypLam.lamN_le (h : HypLam P.k P.r lam c g b) :
    ∀ s, 1 ≤ s → s ≤ P.k + 2 * P.r + 1 → |lamN lam s| ≤ b := by sorry
