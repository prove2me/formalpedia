-- Prove2me | Theorems.Thm_CompanionTheory_WaveGrid_Inhab_nq_minus
-- name    : CompanionTheory.WaveGrid.Inhab.nq_minus
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T07:26:50.779393+00:00
-- url     : https://prove2.me/theorems/5d47c32c-fb28-5e5a-bd2c-642ae94100ae
-- title:
--   Inhab: nq minus
-- statement:
--   The Inhab construction uses the nq minus property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/BesselWaveGrids/NqOfLamData.lean#L125-L151
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/BesselWaveGrids/NqOfLamData.lean#L125-L151

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

theorem CompanionTheory.WaveGrid.Inhab.nq_minus (k r : ℕ) (T T' : ℝ) (hT : 0 < T) (hT' : 0 < T') (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ)
    (c g b : ℝ) (h : HypLam k r lam c g b) (hu : HypType k r lam u b) (l n₀ : ℕ) (hl1 : 1 ≤ l) (hlk : l < k)
    (hposition : (2 * n₀ + 1 : ℝ) ≤ u l - u (l + 1)) (Y : Finset ℝ)
    (hY : ∀ y ∈ Y, u l - n₀ + 2 ≤ -y ∧ -y ≤ u l - 2) :
    NQ ⟨k, r, T, T', u, uM u l n₀⟩ (PStar lam c) Y (nqΛ ⟨k, r, T, T', u, uM u l n₀⟩ b) := by sorry
