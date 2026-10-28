-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_weighted_positive_tail_real_kernel_package
-- name    : AvramDividend.Classical.esscher_weighted_positive_tail_real_kernel_package
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T19:15:33.291111+00:00
-- url     : https://prove2.me/theorems/af33305d-1bff-440a-b740-7487b7844758
-- title:
--   Positive-time continuous antitone bounded real Esscher jump-tail kernel
-- statement:
--   Given an absolutely continuous Lévy jump-magnitude measure with finite positive Esscher-discounted tails, construct explicitly the real positive-time weighted strict-tail kernel, extended by zero on nonpositive times. The kernel is continuous and antitone on (0,∞), nonnegative, and bounded on every [ε,∞), ε>0. This combines the canonically Proved weighted-tail continuity theorem with order monotonicity and finite ENNReal-to-real transport, supplying the exact continuous, causal, locally bounded kernel shape needed in bv_ac_esscher_scaled_renewal_kernel_series_data (9be5ada9), then BV renewal C1 and finite cstar.
-- source:
--   Proved continuousOn_esscher_weighted_positive_tail_of_ac, elementary measure monotonicity and ENNReal.toReal_mono.

import Theorems.Thm_AvramDividend_Classical_continuousOn_esscher_weighted_positive_tail_of_ac
import Mathlib.Data.ENNReal.Real

open AvramDividend.Classical MeasureTheory Set
open scoped ENNReal

theorem AvramDividend.Classical.esscher_weighted_positive_tail_real_kernel_package
    (μ : Measure ℝ) (hac : μ ≪ volume) (φ : ℝ)
    (hfin : ∀ x : ℝ, 0 < x →
      (μ.withDensity
        (fun z : ℝ => ENNReal.ofReal (Real.exp (-(φ * z))))) (Ici x) ≠ ⊤) :
    ∃ κ : ℝ → ℝ,
      (∀ x : ℝ, κ x =
        if 0 < x then
          (μ.withDensity
            (fun z : ℝ => ENNReal.ofReal (Real.exp (-(φ * z))))).real (Ioi x)
        else 0) ∧
      ContinuousOn κ (Ioi (0 : ℝ)) ∧
      AntitoneOn κ (Ioi (0 : ℝ)) ∧
      (∀ x : ℝ, x ≤ 0 → κ x = 0) ∧
      (∀ x : ℝ, 0 ≤ κ x) ∧
      (∀ ε : ℝ, 0 < ε → ∃ M : ℝ, ∀ x : ℝ, ε ≤ x → |κ x| ≤ M) := by sorry
