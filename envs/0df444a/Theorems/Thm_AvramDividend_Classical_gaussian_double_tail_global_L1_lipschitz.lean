-- Prove2me | Theorems.Thm_AvramDividend_Classical_gaussian_double_tail_global_L1_lipschitz
-- name    : AvramDividend.Classical.gaussian_double_tail_global_L1_lipschitz
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T20:49:02.002788+00:00
-- url     : https://prove2.me/theorems/2742e1d2-62c5-4aae-8d62-228f673a476d
-- title:
--   Finite global L1 time-Lipschitz modulus for Gaussian double tails
-- statement:
--   For a Levy jump measure satisfying the truncated-square condition, the full-measure L1 difference of Gaussian Esscher double-tail atoms at positive times s,t is bounded by |t-s| times finite Esscher weight on the positive tail above epsilon. This remains true for infinite-activity small jumps because both atoms vanish below epsilon. The result combines the tail Lipschitz bound with the exact support identity.
-- source:
--   Requires Proved gaussian_double_tail_time_difference_support and gaussian_double_tail_positive_tail_L1_lipschitz.

import Mathlib
open MeasureTheory Set
open scoped ENNReal

theorem AvramDividend.Classical.gaussian_double_tail_global_L1_lipschitz
    (μ : Measure ℝ) (ε φ s t : ℝ)
    (hε : 0 < ε) (hφ : 0 < φ)
    (hs : ε ≤ s) (ht : ε ≤ t)
    (hlevy : (∫⁻ z in Ioi (0 : ℝ),
      ENNReal.ofReal (min 1 (z ^ 2)) ∂μ) < ⊤) :
    (∫⁻ z : ℝ, ENNReal.ofReal
      (|(if 0 < t ∧ t < z then (z - t) * Real.exp (-φ * z) else 0) -
        (if 0 < s ∧ s < z then (z - s) * Real.exp (-φ * z) else 0)|) ∂μ) ≤
    ENNReal.ofReal (|t - s|) *
      (∫⁻ z in Ici ε, ENNReal.ofReal (Real.exp (-φ * z)) ∂μ) ∧
    ENNReal.ofReal (|t - s|) *
      (∫⁻ z in Ici ε, ENNReal.ofReal (Real.exp (-φ * z)) ∂μ) < ⊤ := by sorry
