-- Prove2me | Theorems.Thm_AppliedSDE_SarkkaSolin_gaussian_forward_backward_kernel_symmetry
-- name    : AppliedSDE.SarkkaSolin.gaussian_forward_backward_kernel_symmetry
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T11:36:54.119211+00:00
-- url     : https://prove2.me/theorems/1bb1abfc-487e-4182-aeac-f171dd246d93
-- title:
--   Gaussian transition-density forward-backward kernel symmetry under time and drift reversal
-- statement:
--   The backward Gaussian transition kernel with drift b, fixed terminal point x and time t, is the forward Gaussian kernel with drift -b and starting point x when the time and space axes are reversed. At the fixed initial time s, their spatial profiles agree; at the fixed starting spatial point y, the backward time profile equals the forward time profile at s+t-u. The equality follows from reflection of the squared Gaussian displacement.
-- source:
--   Sarkka and Solin (2019), forward/backward Kolmogorov Gaussian kernel; supports backward theorem 0fda7328-b552-40b9-83b5-e9d2e94d9332.

import Mathlib
open MeasureTheory
open scoped Topology

theorem AppliedSDE.SarkkaSolin.gaussian_forward_backward_kernel_symmetry
    (b q y s x t : ℝ) :
    let B : ℝ -> ℝ -> ℝ := fun z u =>
      Real.exp (-((x - z - b * (t - u)) ^ 2 / (2 * q * (t - u)))) /
        Real.sqrt (2 * Real.pi * q * (t - u))
    let F : ℝ -> ℝ -> ℝ := fun z tau =>
      Real.exp (-((z - x - (-b) * (tau - s)) ^ 2 /
        (2 * q * (tau - s)))) /
        Real.sqrt (2 * Real.pi * q * (tau - s))
    (∀ z : ℝ, B z s = F z t) ∧
      (∀ u : ℝ, B y u = F y (s + t - u)) := by
  sorry
