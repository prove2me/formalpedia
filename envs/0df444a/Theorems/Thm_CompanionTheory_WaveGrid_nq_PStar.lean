-- Prove2me | Theorems.Thm_CompanionTheory_WaveGrid_nq_PStar
-- name    : CompanionTheory.WaveGrid.nq_PStar
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T07:17:27.896959+00:00
-- url     : https://prove2.me/theorems/b749e890-046e-5403-9522-a8881adb00db
-- title:
--   Wave Grid: nq PStar
-- statement:
--   The Wave Grid construction uses the nq PStar property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/BesselWaveGrids/PStarTie.lean#L128-L137
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/BesselWaveGrids/PStarTie.lean#L128-L137

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

theorem CompanionTheory.WaveGrid.nq_PStar (P : M.Par) (hOK : P.OK) (l : ℕ) (hl1 : 1 ≤ l) (hlk : l ≤ P.k) (hk : 2 ≤ P.k)
    (lam : Fin (2 * P.r + P.k + 1) → ℝ) (c g b : ℝ) (hL : PairData P l (lamN lam) c g b) (Y : Finset ℝ)
    (hY : ∀ y ∈ Y, I.OnCut P.u P.u' l y) : NQ P (PStar lam c) Y (nqΛ P b) := by sorry
