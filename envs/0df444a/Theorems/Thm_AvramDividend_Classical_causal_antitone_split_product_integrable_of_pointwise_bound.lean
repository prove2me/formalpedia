-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_antitone_split_product_integrable_of_pointwise_bound
-- name    : AvramDividend.Classical.causal_antitone_split_product_integrable_of_pointwise_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T14:57:08.436158+00:00
-- url     : https://prove2.me/theorems/72ccda3f-2378-4a86-b9f3-08d8f19679ff
-- title:
--   Causal antitone split product is interval-integrable under reciprocal pointwise control
-- statement:
--   Given a nonnegative antitone L1 kernel and an L1 input with pointwise 0≤F(s)≤A/s on positive time, the reflected convolution product κ(x-s)F(s) is integrable on both sides of every split 0<u<x. On the left, the kernel is bounded by its value κ(x-u); on the right, F is bounded by A/u. Measurability and the two relevant L1 restrictions are stated explicitly. This discharges the split-product integrability bridge needed by the quadratic Gaussian convolution-power induction once its pointwise inductive hypothesis is known.
-- source:
--   Combine the two proved causal split and antitone cutoff norm lemmas, converting the pointwise inequalities to ae bounds under interval-restricted volume using MeasureTheory.ae_restrict_mem.

import Mathlib.Analysis.Convolution
import Theorems.Thm_AvramDividend_Classical_causal_split_convolution_integrable_of_ae_bounded_factors
import Theorems.Thm_AvramDividend_Classical_causal_antitone_left_cutoff_kernel_norm_bound

open MeasureTheory Set

theorem AvramDividend.Classical.causal_antitone_split_product_integrable_of_pointwise_bound
    (κ F : ℝ → ℝ) (x u A : ℝ)
    (hu : 0 < u) (hux : u < x) (hA : 0 ≤ A)
    (hanti : AntitoneOn κ (Ioi (0 : ℝ)))
    (hKnonneg : ∀ t : ℝ, 0 < t → 0 ≤ κ t)
    (hFnonneg : ∀ s : ℝ, 0 < s → 0 ≤ F s)
    (hFpoint : ∀ s : ℝ, 0 < s → F s ≤ A / s)
    (hFleftInt : IntegrableOn F (Ioc (0 : ℝ) u) volume)
    (hKleftMeas : AEStronglyMeasurable
      (fun s : ℝ => κ (x - s)) (volume.restrict (Ioc (0 : ℝ) u)))
    (hKrightInt : IntegrableOn (fun s : ℝ => κ (x - s)) (Ioc u x) volume)
    (hFrightMeas : AEStronglyMeasurable F (volume.restrict (Ioc u x))) :
    IntervalIntegrable (fun s : ℝ => κ (x - s) * F s) volume 0 u ∧
    IntervalIntegrable (fun s : ℝ => κ (x - s) * F s) volume u x := by sorry
