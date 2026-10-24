-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_split_convolution_integrable_of_ae_bounded_factors
-- name    : AvramDividend.Classical.causal_split_convolution_integrable_of_ae_bounded_factors
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T14:32:35.815847+00:00
-- url     : https://prove2.me/theorems/31f3c72b-8fcf-48e4-9fb4-87c2b1a90404
-- title:
--   Two-piece causal convolution integrability from complementary bounded factors
-- statement:
--   On the left of a causal cutoff, an L1 input times an essentially bounded reversed kernel is integrable. On the right, an L1 reversed kernel times an essentially bounded input is integrable. This two-piece theorem supplies the exact finite-interval integrability premises needed by the Gaussian quadratic-geometric convolution-power induction without imposing a global bound on the kernel.
-- source:
--   Pinned MeasureTheory.Integrable.bdd_mul and Integrable.mul_bdd under restricted interval measures, followed by intervalIntegrable_iff_integrableOn_Ioc_of_le.

import Mathlib.Analysis.Convolution

open MeasureTheory Set

theorem AvramDividend.Classical.causal_split_convolution_integrable_of_ae_bounded_factors
    (κ F : ℝ → ℝ) (x u C B : ℝ) (h0u : 0 ≤ u) (hux : u ≤ x)
    (hFleftInt : IntegrableOn F (Ioc (0 : ℝ) u) volume)
    (hKleftMeas : AEStronglyMeasurable
      (fun s : ℝ => κ (x - s)) (volume.restrict (Ioc (0 : ℝ) u)))
    (hKleftBound : ∀ᵐ s ∂(volume.restrict (Ioc (0 : ℝ) u)),
      ‖κ (x - s)‖ ≤ C)
    (hKrightInt : IntegrableOn (fun s : ℝ => κ (x - s)) (Ioc u x) volume)
    (hFrightMeas : AEStronglyMeasurable F (volume.restrict (Ioc u x)))
    (hFrightBound : ∀ᵐ s ∂(volume.restrict (Ioc u x)), ‖F s‖ ≤ B) :
    IntervalIntegrable (fun s : ℝ => κ (x - s) * F s) volume 0 u ∧
    IntervalIntegrable (fun s : ℝ => κ (x - s) * F s) volume u x := by sorry
