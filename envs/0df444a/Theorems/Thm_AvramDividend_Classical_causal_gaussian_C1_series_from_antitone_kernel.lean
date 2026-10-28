-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_gaussian_C1_series_from_antitone_kernel
-- name    : AvramDividend.Classical.causal_gaussian_C1_series_from_antitone_kernel
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T19:55:25.373879+00:00
-- url     : https://prove2.me/theorems/11e17869-c3bc-4274-b2a9-3112d315d901
-- title:
--   Explicit C1 derivative-resolvent candidate for a Gaussian antitone L1 kernel
-- statement:
--   Any nonnegative, nonincreasing, positive-time continuous integrable Gaussian-type kernel and positive diffusion coefficient determine an exponentially damped signed convolution series. Its explicitly integrated Neumann sum is continuous on nonnegative time and C1 on positive time.
-- source:
--   Compose the contracting Gaussian antitone envelope power theorem, the proved signed causal kernel construction, and the accepted C1 signed-Neumann-series existence theorem. The remaining separate obligation is the exact Volterra integral resolvent identity for this g.

import Theorems.Thm_AvramDividend_Classical_causal_damped_antitone_envelope_quadratic
import Theorems.Thm_AvramDividend_Classical_causal_weighted_antitone_kernel
import Theorems.Thm_AvramDividend_Classical_causal_weighted_kernel_continuous_positive
import Theorems.Thm_AvramDividend_Classical_causal_gaussian_signed_damped_kernel_data
import Theorems.Thm_AvramDividend_Classical_causal_neumann_C1_from_antitone_envelope_powers

open AvramDividend.Classical MeasureTheory Set

theorem AvramDividend.Classical.causal_gaussian_C1_series_from_antitone_kernel
    (K : ℝ → ℝ) (a β : ℝ) (ha : 0 < a)
    (hK : IntegrableOn K (Ioi (0 : ℝ)) volume)
    (hKpos : ∀ t : ℝ, 0 ≤ t → 0 ≤ K t)
    (hKanti : AntitoneOn K (Ioi (0 : ℝ)))
    (hKcont : ContinuousOn K (Ioi (0 : ℝ))) :
    ∃ (w : ℝ) (k : ℝ → ℝ) (P : ℕ → ℝ → ℝ) (g : ℝ → ℝ),
      0 < w ∧
      k = (fun t : ℝ =>
        if 0 < t then -(a⁻¹ * Real.exp (-w * t) * (β + K t)) else 0) ∧
      P 0 = k ∧
      (∀ n : ℕ, P (n + 1) =
        fun x : ℝ => ∫ s in Ioc (0 : ℝ) x, k s * P n (x - s) ∂volume) ∧
      (g = fun y : ℝ => 1 / a + Real.exp (w * y) *
        (∑' n : ℕ, (Real.exp (-w * y) *
          (∫ s in Ioc (0 : ℝ) y,
            Real.exp (w * s) * P n s ∂volume)) / a)) ∧
      ContinuousOn g (Ici (0 : ℝ)) ∧
      ContDiffOn ℝ 1 g (Ioi (0 : ℝ)) := by sorry
