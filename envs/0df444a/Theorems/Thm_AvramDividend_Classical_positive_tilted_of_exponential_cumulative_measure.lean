-- Prove2me | Theorems.Thm_AvramDividend_Classical_positive_tilted_of_exponential_cumulative_measure
-- name    : AvramDividend.Classical.positive_tilted_of_exponential_cumulative_measure
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-04T00:21:22.086948+00:00
-- url     : https://prove2.me/theorems/e0ac041c-6799-42ca-8c11-9b5de793ba86
-- title:
--   Strict positivity and exponential tilted monotonicity from a cumulative measure
-- statement:
--   For any nonnegative measure with positive mass at zero, finite cumulative mass on each positive half-line, and an exponential cumulative representation W(x)=exp(φx)β((−∞,x]) for x>0 with φ>0, W is strictly positive on x>0 and exp(−φx)W(x) is nondecreasing on the positive half-line. This is the exact final deterministic bridge needed once the spectrally negative bounded-variation Lévy renewal resolvent is factored into an exponential kernel convolution with a positive measure. It requires neither differentiability nor density regularity.
-- source:
--   Pinned Mathlib MeasureTheory.Measure real CDF monotonicity from measure_mono and ENNReal.toReal_mono; Real.exp_add and Real.exp_pos

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

/-- A strictly positive cumulative measure, multiplied by an exponential,
automatically satisfies the positive exponentially tilted monotonicity bridge. -/
theorem positive_tilted_of_exponential_cumulative_measure (β : Measure ℝ) (φ : ℝ) (hφ : 0 < φ)
    (hfin : ∀ x : ℝ, 0 < x → β (Iic x) ≠ ⊤)
    (hatom : 0 < β {0})
    (W : ℝ → ℝ)
    (hW : ∀ x : ℝ, 0 < x →
      W x = Real.exp (φ * x) * (β (Iic x)).toReal) :
    (∀ x : ℝ, 0 < x → 0 < W x) ∧
      MonotoneOn (fun x : ℝ => Real.exp (-φ * x) * W x) (Ioi 0) := by
  sorry

end AvramDividend.Classical
