-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_finite_band_centered_l2_limit_preserves_zero_mean
-- name    : AvramDividend.Classical.avram_wave4_p1_finite_band_centered_l2_limit_preserves_zero_mean
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T22:42:20.737929+00:00
-- url     : https://prove2.me/theorems/b028e313-614f-4b68-8824-c477c323055b
-- title:
--   Infinite-activity stopped L² limit preserves centered expectation from the original finite-band integrals
-- statement:
--   If the actual finite-band compensated integrals have the source-verified pairwise L² increment bound and zero expectation for each band, then their complete L² limit exists and remains centered. Formally the expected-value map is represented by any continuous real-valued functional φ on the complete space W; the source must identify the expectation functional and prove finite-band φ(M_n)=0. The statement assumes no mean-zero property for the limit and no Campbell identity as a premise, and passes the finite-band stochastic structure to the same original probability space by continuity.
-- source:
--   P1 complete finite-band limit theorem ba154790 (authoring pending initially); pinned Mathlib Continuous.tendsto and tendsto_nhds_unique.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_finite_band_l2_increment_bound_yields_complete_stopped_limit

open MeasureTheory Set Filter Topology
open scoped ENNReal

theorem AvramDividend.Classical.avram_wave4_p1_finite_band_centered_l2_limit_preserves_zero_mean
    {α W : Type*} [MeasurableSpace α]
    [MetricSpace W] [CompleteSpace W]
    (μ : Measure α)
    (f : α → ℝ) (hf : Measurable f)
    (henergy : ∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂μ < ∞)
    (B : ℕ → Set α) (hB : ∀ n, MeasurableSet (B n))
    (hBfinite : ∀ n, μ (B n) < ∞)
    (hBmono : Monotone B) (hBcover : (⋃ n, B n) = Set.univ)
    (M : ℕ → W)
    (hfinite_band_isometry_bound :
      ∀ m n, m ≤ n →
        dist (M m) (M n) ≤
          (eLpNorm ((B m)ᶜ.indicator f) (2 : ℝ≥0∞) μ).toReal)
    (φ : W → ℝ) (hφ : Continuous φ)
    (hcentered : ∀ n, φ (M n) = 0) :
    ∃ Mlimit : W,
      Tendsto M Filter.atTop (nhds Mlimit) ∧ φ Mlimit = 0 := by sorry
