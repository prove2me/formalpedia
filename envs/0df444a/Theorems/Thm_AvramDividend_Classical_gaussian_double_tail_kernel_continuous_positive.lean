-- Prove2me | Theorems.Thm_AvramDividend_Classical_gaussian_double_tail_kernel_continuous_positive
-- name    : AvramDividend.Classical.gaussian_double_tail_kernel_continuous_positive
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T21:07:13.846091+00:00
-- url     : https://prove2.me/theorems/c8a5bad9-41a4-4161-b6b3-e34a658dde1d
-- title:
--   Continuity of the integrated Gaussian Esscher double-tail kernel at positive times
-- statement:
--   Under the Levy truncated-square condition and positive Esscher parameter, the nonnegative integrated Gaussian double-tail kernel is continuous at every strictly positive time. Pointwise time continuity, positive-time antitonicity and a finite dominating kernel at half the time allow application of the dominated-convergence theorem for nonnegative extended-real integrals.
-- source:
--   Requires Proved gaussian_double_tail_atom_continuous_time, gaussian_double_tail_atom_antitone and gaussian_double_tail_kernel_finite_positive. Uses exact-pinned tendsto_lintegral_filter_of_dominated_convergence.

import Mathlib
open MeasureTheory Set Filter Topology
open scoped ENNReal

theorem AvramDividend.Classical.gaussian_double_tail_kernel_continuous_positive
    (μ : Measure ℝ) [SFinite μ] (φ : ℝ) (hφ : 0 < φ)
    (hlevy : (∫⁻ z in Ioi (0 : ℝ),
      ENNReal.ofReal (min 1 (z ^ 2)) ∂μ) < ⊤)
    (t : ℝ) (ht : 0 < t) :
    ContinuousAt (fun u : ℝ => ∫⁻ z : ℝ,
      (if 0 < u ∧ u < z then
        ENNReal.ofReal (z - u) * ENNReal.ofReal (Real.exp (-φ * z))
       else 0) ∂μ) t := by sorry
