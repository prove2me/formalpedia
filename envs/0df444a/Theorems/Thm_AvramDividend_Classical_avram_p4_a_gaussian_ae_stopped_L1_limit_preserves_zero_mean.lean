-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_ae_stopped_L1_limit_preserves_zero_mean
-- name    : AvramDividend.Classical.avram_p4_a_gaussian_ae_stopped_L1_limit_preserves_zero_mean
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T21:32:49.211449+00:00
-- url     : https://prove2.me/theorems/3a48374d-301f-4062-86e0-8c5ee77f2353
-- title:
--   Stopped continuous-martingale finite sums preserve zero expectation through genuine L1 convergence
-- statement:
--   When each finite stopped continuous-martingale Gaussian sum is integrable with zero expected value and its random-variable sequence converges in actual L1 to a strongly measurable limit, the limiting stopped Gaussian residual has expected value zero. This is the exact expectation passage needed after source-specific Gaussian extraction and genuine Ito convergence. It introduces no Brownian process, semimartingale representation, derivative bound or L1 convergence assumption without evidence.
-- source:
--   Mathlib.MeasureTheory.Integral.Bochner.Basic tendsto_integral_of_L1 combined with uniqueness of limits in a Hausdorff space. The hypotheses expose all analytic obligations rather than conceal them.

import Mathlib
open MeasureTheory Filter
open scoped ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_a_gaussian_ae_stopped_L1_limit_preserves_zero_mean
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (F : ℕ → Ω → ℝ) (f : Ω → ℝ)
    (hf : AEStronglyMeasurable f P)
    (hFI : ∀ n, Integrable (F n) P)
    (hzero : ∀ n, (∫ ω, F n ω ∂P) = 0)
    (hL1 : Tendsto (fun n => ∫⁻ ω, ‖F n ω - f ω‖ₑ ∂P)
      atTop (nhds 0)) :
    (∫ ω, f ω ∂P) = 0 := by sorry
