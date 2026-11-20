-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_A_original_finite_barrier_first_size2_mark_ruin_time_exact
-- name    : AvramDividend.Classical.avram_jump6_A_original_finite_barrier_first_size2_mark_ruin_time_exact
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T11:16:34.094038+00:00
-- url     : https://prove2.me/theorems/a48667b3-82a0-43da-8e3b-b468a457b476
-- title:
--   The original finite-cap Brownian-size-two-Poisson ruin clock equals the actual first negative mark on a small tube
-- statement:
--   On the true original Brownian−2N Lévy path with reserve x=1/10 and capped barrier a=1/5, assume the physical Brownian path stays inside 1/4000 until its first negative mark σ, there are no negative marks before σ and at least one occurs at σ. Then the actual original ruinTime with the true barrierStrategy equals σ exactly. The original barrier pays zero before crossing the cap, the reserve remains strictly positive before σ, and the actual size-two jump makes the controlled risk strictly negative at σ. This bridges the positive physical first-mark event to the genuine ruin-clipped stopping clock and correct right-closed dividend convention for the 061f full-mark source countermodel.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option autoImplicit false
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_jump6_A_original_finite_barrier_first_size2_mark_ruin_time_exact
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (B : ℝ≥0 → ℝ) (N : ℝ≥0 → ℕ)
    (σ : ℝ≥0)
    (hPath : ∀ t : ℝ≥0, X.X t ω = B t - 2 * (N t : ℝ))
    (hTube : ∀ t : ℝ≥0, t ≤ σ → |B t| < (1 / 4000 : ℝ))
    (hBefore : ∀ t : ℝ≥0, t < σ → N t = 0)
    (hMark : 1 ≤ N σ) :
    ruinTime X (1 / 10 : ℝ)
      (barrierStrategy X (1 / 10 : ℝ) (1 / 5 : ℝ)) ω =
      (σ : ℝ≥0∞) := by sorry
