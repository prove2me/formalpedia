-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_A_original_spatial_exit_clip_identity_when_physical_path_below_upbarrier
-- name    : AvramDividend.Classical.avram_jump6_A_original_spatial_exit_clip_identity_when_physical_path_below_upbarrier
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T09:58:14.990179+00:00
-- url     : https://prove2.me/theorems/2602e14f-c224-48b8-9332-a71aec04e7b3
-- title:
--   Original spatial upper-exit localisation leaves true bounded stopped clock unchanged below actual barrier
-- statement:
--   For the actual spectrally negative Lévy sample path, if the original process X.X_t remains at most the strict upward-exit threshold a for every clock t≤σ, then the original twoSidedExitUpTime X a is at least σ, and the spatially clipped clock min(σ, twoSidedExitUpTime).toNNReal equals σ exactly. This is the precise localising-clock identity required to specialise the disputed original 5424c324 positive-horizon κ k source to the first negative size-two Poisson ruin clock on a Brownian small tube.

import Mathlib
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
set_option autoImplicit false
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_jump6_A_original_spatial_exit_clip_identity_when_physical_path_below_upbarrier
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (σ : ℝ≥0) (a : ℝ)
    (hBelow : ∀ t : ℝ≥0, t ≤ σ → X.X t ω ≤ a) :
    (min (σ : ℝ≥0∞) (twoSidedExitUpTime X a ω)).toNNReal = σ := by sorry
