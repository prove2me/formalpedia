-- Prove2me | Theorems.Thm_CompanionTheory_WaveGrid_HypLam_k_le
-- name    : CompanionTheory.WaveGrid.HypLam.k_le
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T06:59:34.316416+00:00
-- url     : https://prove2.me/theorems/76a56f0e-bb23-43eb-aa5a-3286247795fd
-- title:
--   Hyp Lam: k le
-- statement:
--   The Hyp Lam construction uses the k le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/BesselWaveGrids/PStarTie.lean#L79-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/BesselWaveGrids/PStarTie.lean#L79-L82

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

theorem CompanionTheory.WaveGrid.HypLam.k_le (h : HypLam P.k P.r lam c g b) : (P.k : ℝ) ≤ b := by sorry
