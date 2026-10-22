-- Prove2me | Theorems.Thm_AvramDividend_Classical_gaussian_double_tail_kernel_finite_positive
-- name    : AvramDividend.Classical.gaussian_double_tail_kernel_finite_positive
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T08:11:17.910201+00:00
-- url     : https://prove2.me/theorems/7f11bc5c-2df9-4be9-bd20-764638a3e9b1
-- title:
--   Finiteness of the Gaussian Esscher double-tail at every positive time
-- statement:
--   For a positive jump-magnitude measure satisfying the Lévy truncated-square condition and any positive Esscher cutoff φ, the unweighted double-tail kernel Rφ(t)=∫_{z>t}(z−t)e^(−φz) μ(dz) is finite at every strictly positive t. The already established almost-everywhere finiteness and monotonicity combine via the positive measure of (0,t), the pinned measure-theoretic a.e. witness lemma, and comparison with an earlier finite time. This prepares a real-valued Volterra renewal kernel; continuity and Gaussian scale regularity remain separate obligations.
-- source:
--   Requires Proved gaussian_double_tail_unweighted_kernel_ae_finite and gaussian_double_tail_kernel_antitone; exact-pinned Measure.exists_mem_of_measure_ne_zero_of_ae, ae_restrict_of_ae, Real.volume_Ioo.

import Mathlib
open MeasureTheory Set
open scoped ENNReal

theorem AvramDividend.Classical.gaussian_double_tail_kernel_finite_positive
    (μ : Measure ℝ) [SFinite μ] (φ : ℝ) (hφ : 0 < φ)
    (hlevy : (∫⁻ z in Ioi (0 : ℝ),
      ENNReal.ofReal (min 1 (z ^ 2)) ∂μ) < ⊤)
    (t : ℝ) (ht : 0 < t) :
    (∫⁻ z : ℝ,
      (if 0 < t ∧ t < z then
        ENNReal.ofReal (z - t) * ENNReal.ofReal (Real.exp (-φ * z))
       else 0) ∂μ) < ⊤ := by sorry
