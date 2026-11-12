-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB118_bounded_ae_L2_loss_tendsto
-- name    : AvramDividend.Classical.avram_gbB118_bounded_ae_L2_loss_tendsto
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T00:09:47.634104+00:00
-- url     : https://prove2.me/theorems/64aae74c-a086-4a00-8d3e-a5f9d21b2816
-- title:
--   Dominated bounded almost-everywhere limit gives L2 square-loss convergence
-- statement:
--   For any finite measure, a sequence of almost-everywhere measurable real functions uniformly bounded in absolute value by B, with an a.e. limit g likewise bounded by B, has squared error integral tending to zero. This is the reusable dominated-convergence analytic step required to turn B102 sampled Gaussian coefficient convergence into B116 physical time-probability L2 convergence. It does not change any stochastic model.

import Mathlib
open MeasureTheory Filter Topology
noncomputable section

theorem AvramDividend.Classical.avram_gbB118_bounded_ae_L2_loss_tendsto
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ]
    (f : ℕ → α → ℝ) (g : α → ℝ)
    (hf : ∀ m, AEStronglyMeasurable (f m) μ)
    (hg : AEStronglyMeasurable g μ)
    (B : ℝ) (hB : 0 ≤ B)
    (hfb : ∀ m, ∀ᵐ a ∂μ, |f m a| ≤ B)
    (hgb : ∀ᵐ a ∂μ, |g a| ≤ B)
    (hae : ∀ᵐ a ∂μ,
      Tendsto (fun m => f m a) atTop (𝓝 (g a))) :
    Tendsto (fun m => ∫ a, (f m a - g a) ^ 2 ∂μ)
      atTop (𝓝 (0 : ℝ)) := by sorry
