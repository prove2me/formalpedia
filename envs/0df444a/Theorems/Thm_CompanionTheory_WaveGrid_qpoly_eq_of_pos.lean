-- Prove2me | Theorems.Thm_CompanionTheory_WaveGrid_qpoly_eq_of_pos
-- name    : CompanionTheory.WaveGrid.qpoly_eq_of_pos
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T06:28:16.063882+00:00
-- url     : https://prove2.me/theorems/d3c9397a-4ab6-5c03-9ae2-6d3e20140a68
-- title:
--   Wave Grid: qpoly eq of pos
-- statement:
--   The Wave Grid construction uses the qpoly eq of pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/BesselWaveGrids/NQText.lean#L49-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/BesselWaveGrids/NQText.lean#L49-L55

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Interlace
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselWaveGrids_QwBound
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselWaveGrids_InterlacingGrids_PstMul
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselWaveGrids_NQText
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory CompanionTheory.WaveGrid
open Formalism.FourierDecayAlt Finset

theorem CompanionTheory.WaveGrid.qpoly_eq_of_pos (k : ℕ) (T T' : ℝ) (u u' : ℕ → ℝ) (Y : ℝ) (hT : 0 < T) (hT' : 0 < T')
    (hq : 0 < I.qpoly k T T' u u' Y) :
    I.qpoly k T T' u u' Y = T * T' * ∏ i ∈ Icc 1 k, (|Y + 1 / 2 + u i| * |Y + 1 / 2 + u' i|) := by sorry
