-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_A_original_all_spatial_kappa_equal_first_negative_mark_on_real_BrownianPoisson_tube
-- name    : AvramDividend.Classical.avram_jump6_A_original_all_spatial_kappa_equal_first_negative_mark_on_real_BrownianPoisson_tube
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T15:46:35.379686+00:00
-- url     : https://prove2.me/theorems/1c09a08b-0090-4b42-b317-40be418e1b33
-- title:
--   Every original spatial upper-exit localisation clock reaches the true first ruin-causing size-two negative mark on the physical small Brownian tube
-- statement:
--   On an actual X=B−2N spectrally negative Lévy sample path with one first negative size-two Poisson mark at σ and a uniformly small Brownian fluctuation until σ, the original X path lies below 1/10 on [0,σ]. Every spatial upper-exit threshold k+1≥1 is therefore unattained before σ. If the genuine ruin-clipped ρ equals σ, the exact κ_k=min(ρ,upper-exit time to k+1) equals σ for all spatial k, not merely one mesh. This is the missing real-process, all-spatial-level clock identification required to apply the original Hsource on its true early ruin event.

import Mathlib
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_avram_jump6_A_actual_Brownian_negative_mark_tube_forces_ruin_without_upper_cap_exit
import Theorems.Thm_AvramDividend_Classical_avram_jump6_A_original_spatial_exit_clip_identity_when_physical_path_below_upbarrier
set_option autoImplicit false
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_jump6_A_original_all_spatial_kappa_equal_first_negative_mark_on_real_BrownianPoisson_tube
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (B : ℝ≥0 → ℝ) (N : ℝ≥0 → ℕ)
    (σ : ℝ≥0) (ρ : Ω → ℝ≥0)
    (κ : ℕ → Ω → ℝ≥0)
    (hPath : ∀ t : ℝ≥0, X.X t ω = B t - 2 * (N t : ℝ))
    (hTube : ∀ t : ℝ≥0, t ≤ σ → |B t| < (1 / 4000 : ℝ))
    (hMark : 1 ≤ N σ)
    (hρ : ρ ω = σ)
    (hκ : ∀ k, κ k ω =
      (min (ρ ω : ℝ≥0∞)
        (twoSidedExitUpTime X ((k : ℝ) + 1) ω)).toNNReal) :
    ∀ k : ℕ, κ k ω = σ := by sorry
