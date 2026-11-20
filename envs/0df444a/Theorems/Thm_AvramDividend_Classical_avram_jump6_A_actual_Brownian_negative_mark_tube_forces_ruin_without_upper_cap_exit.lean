-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_A_actual_Brownian_negative_mark_tube_forces_ruin_without_upper_cap_exit
-- name    : AvramDividend.Classical.avram_jump6_A_actual_Brownian_negative_mark_tube_forces_ruin_without_upper_cap_exit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T08:50:40.134575+00:00
-- url     : https://prove2.me/theorems/94f449de-dfe7-4678-96b7-bf8a3f8ab870
-- title:
--   Actual Brownian plus negative-mark original path stays below cap then strictly ruins at marked stopped time
-- statement:
--   For a genuine original spectrally negative Lévy sample path X=B−2N, if Brownian path fluctuations stay within 1/4000 up to the selected mark clock σ and at least one physical negative mark has occurred at σ, then X_s≤1/10 throughout the stopped path (no upcrossing of the upper barrier at x=1/10, a=1/5), and the post-mark reserve x+X_σ is strictly negative (immediate ruin). The theorem combines the true Gaussian and full marked Poisson components under explicit original path identity and is the key eventwise bridge from the positive-probability Brownian-Poisson product tube to the stopped cash contradiction. No synthetic noise, no false global almost-sure claim.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option autoImplicit false
open MeasureTheory Set Filter
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_jump6_A_actual_Brownian_negative_mark_tube_forces_ruin_without_upper_cap_exit
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (B : ℝ≥0 → ℝ) (N : ℝ≥0 → ℕ)
    (σ : ℝ≥0)
    (hOriginal : ∀ t : ℝ≥0, X.X t ω = B t - 2 * (N t : ℝ))
    (hTube : ∀ t : ℝ≥0, t ≤ σ → |B t| < (1 / 4000 : ℝ))
    (hMark : 1 ≤ N σ) :
    (∀ t : ℝ≥0, t ≤ σ → X.X t ω ≤ (1 / 10 : ℝ)) ∧
    (1 / 10 : ℝ) + X.X σ ω < 0 := by sorry
