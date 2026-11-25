-- Prove2me | Theorems.Thm_CompanionTheory_WaveGrid_inter_half
-- name    : CompanionTheory.WaveGrid.inter_half
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T07:08:58.416094+00:00
-- url     : https://prove2.me/theorems/fa7c5e58-9332-43b4-8e30-1051fdef6f6d
-- title:
--   Wave Grid: inter half
-- statement:
--   The Wave Grid construction uses the inter half property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/BesselWaveGrids/PStarTie.lean#L57-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/BesselWaveGrids/PStarTie.lean#L57-L73

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

theorem CompanionTheory.WaveGrid.inter_half {k r : ℕ} {lam : Fin (2 * r + k + 1) → ℝ} (hc : Formalism.QuantumDeterminants.IsHCParam lam) {u : ℕ → ℝ} {b : ℝ}
    (hu : HypType k r lam u b) (s : ℕ) (hs1 : 1 ≤ s) (hsk : s ≤ k - 1) :
    lamN lam s + 1 / 2 ≤ u s ∧ u (s + 1) ≤ lamN lam s - 1 / 2 := by sorry
