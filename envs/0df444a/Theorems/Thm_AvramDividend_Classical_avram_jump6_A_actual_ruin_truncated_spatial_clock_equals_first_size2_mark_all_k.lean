-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_A_actual_ruin_truncated_spatial_clock_equals_first_size2_mark_all_k
-- name    : AvramDividend.Classical.avram_jump6_A_actual_ruin_truncated_spatial_clock_equals_first_size2_mark_all_k
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T15:47:28.743734+00:00
-- url     : https://prove2.me/theorems/f5bb85b0-8d3d-4d21-9fb1-6423e167cf3d
-- title:
--   Actual original ruin-truncated horizon-one physical spatial clocks equal first negative size-two Poisson mark on the Brownian tube at every k
-- statement:
--   Let X=B−2N be the genuine physical Brownian-minus-negative-two-Poisson spectrally negative Lévy path, with its first negative mark at σ≤1/500 and Brownian fluctuation <1/4000 up to σ. For the original capped barrier at reserve 1/10 and cap 1/5, the already-Proved first-mark ruinTime is exactly σ. Therefore the original horizon-one ruin-clipped clock ρ=min(ruinTime,1) equals σ. Meanwhile all original spatial upper-exit thresholds k+1≥1 are inaccessible before σ, so the exact κ_k=min(ρ,upperExit(k+1)) equals σ for all k. This is an explicit source-exact actual-clock identification, eliminating an assumption from previous firstmark clock bridging.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_avram_jump6_A_original_finite_barrier_first_size2_mark_ruin_time_exact
import Theorems.Thm_AvramDividend_Classical_avram_jump6_A_actual_Brownian_negative_mark_tube_forces_ruin_without_upper_cap_exit
import Theorems.Thm_AvramDividend_Classical_avram_jump6_A_original_spatial_exit_clip_identity_when_physical_path_below_upbarrier
set_option autoImplicit false
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_jump6_A_actual_ruin_truncated_spatial_clock_equals_first_size2_mark_all_k
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (B : ℝ≥0 → ℝ) (N : ℝ≥0 → ℕ)
    (σ : ℝ≥0) (ρ : Ω → ℝ≥0)
    (κ : ℕ → Ω → ℝ≥0)
    (hPath : ∀ t : ℝ≥0, X.X t ω = B t - 2 * (N t : ℝ))
    (hTube : ∀ t : ℝ≥0, t ≤ σ → |B t| < (1 / 4000 : ℝ))
    (hBefore : ∀ t : ℝ≥0, t < σ → N t = 0)
    (hMark : 1 ≤ N σ)
    (hSmall : (σ : ℝ) ≤ 1 / 500)
    (hρ : ρ ω =
      (min (ruinTime X (1 / 10 : ℝ)
        (barrierStrategy X (1 / 10 : ℝ) (1 / 5 : ℝ)) ω)
        (1 : ℝ≥0∞)).toNNReal)
    (hκ : ∀ k, κ k ω =
      (min (ρ ω : ℝ≥0∞)
        (twoSidedExitUpTime X ((k : ℝ) + 1) ω)).toNNReal) :
    ∀ k : ℕ, κ k ω = σ := by sorry
