-- Prove2me | Theorems.Thm_CompanionTheory_WaveGrid_den_core
-- name    : CompanionTheory.WaveGrid.den_core
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T06:26:10.078971+00:00
-- url     : https://prove2.me/theorems/c58373a5-9706-4603-9239-13b9c91f9c13
-- title:
--   Wave Grid: den core
-- statement:
--   The Wave Grid construction uses the den core property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/BesselWaveGrids/NQText.lean#L19-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/BesselWaveGrids/NQText.lean#L19-L34

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

theorem CompanionTheory.WaveGrid.den_core (k : ℕ) (u u' ρ : ℕ → ℝ) (l : ℕ) (Y : ℝ) (hl1 : 1 ≤ l) (hlk : l ≤ k)
    (h : I.Interlaces k u u' ρ) (hA : u l + 2 ≤ -Y ∧ -Y ≤ u' l - 2) :
    ∀ i, 1 ≤ i → i ≤ k → 1 ≤ |Y + 1 / 2 + u i| ∧ 1 ≤ |Y + 1 / 2 + u' i| := by sorry
