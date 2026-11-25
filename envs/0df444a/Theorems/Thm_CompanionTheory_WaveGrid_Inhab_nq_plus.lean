-- Prove2me | Theorems.Thm_CompanionTheory_WaveGrid_Inhab_nq_plus
-- name    : CompanionTheory.WaveGrid.Inhab.nq_plus
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T07:15:28.579662+00:00
-- url     : https://prove2.me/theorems/476604d7-b1f1-5bb5-bae7-92a1e60b55a5
-- title:
--   Inhab: nq plus
-- statement:
--   The Inhab construction uses the nq plus property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/BesselWaveGrids/NqOfLamData.lean#L97-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/BesselWaveGrids/NqOfLamData.lean#L97-L123

import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselWaveGrids_PStarTie
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselWaveGrids_CfgTie
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselWaveGrids_NqOfLamData
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory CompanionTheory.WaveGrid CompanionTheory.WaveGrid.Inhab
open Formalism.FourierDecayAlt Finset CompanionTheory.WaveGrid GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid

theorem CompanionTheory.WaveGrid.Inhab.nq_plus (k r : ℕ) (T T' : ℝ) (hT : 0 < T) (hT' : 0 < T') (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ)
    (c g b : ℝ) (h : HypLam k r lam c g b) (hu : HypType k r lam u b) (l n₀ : ℕ) (hl1 : 1 ≤ l) (hlk : l < k)
    (hposition : (2 * n₀ + 1 : ℝ) ≤ u l - u (l + 1)) (Y : Finset ℝ)
    (hY : ∀ y ∈ Y, u (l + 1) + 2 ≤ -y ∧ -y ≤ u (l + 1) + n₀ - 2) :
    NQ ⟨k, r, T, T', u, uP u l n₀⟩ (PStar lam c) Y (nqΛ ⟨k, r, T, T', u, uP u l n₀⟩ b) := by sorry
