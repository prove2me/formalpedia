-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_weighted_sup_contraction_zero
-- name    : AvramDividend.Classical.causal_weighted_sup_contraction_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T21:52:57.652359+00:00
-- url     : https://prove2.me/theorems/25cca399-3b08-49a0-b74a-f2f4d48f29be
-- title:
--   Weighted-supremum contraction forces the zero function on the positive half-line
-- statement:
--   Any function whose exponentially weighted absolute value is bounded on each finite positive interval and is pointwise bounded by a strict contraction factor times its finite-horizon supremum must vanish on all positive times. The proof applies the conditionally complete supremum bound and strict c<1 to force each local supremum to zero. This is the elementary final uniqueness step after the causal Volterra kernel norm inequality.
-- source:
--   Pinned Mathlib le_csSup, csSup_le, real exponential positivity and linear arithmetic; finite-horizon weighted Volterra contraction argument.

import Mathlib
open MeasureTheory Set

theorem AvramDividend.Classical.causal_weighted_sup_contraction_zero
    (D : ℝ → ℝ) (w c : ℝ) (hc : c < 1)
    (hbound : ∀ R : ℝ, 0 < R →
      BddAbove ((fun t : ℝ => Real.exp (-(w * t)) * |D t|) '' Ioc (0 : ℝ) R))
    (hcontraction : ∀ R : ℝ, 0 < R → ∀ t ∈ Ioc (0 : ℝ) R,
      Real.exp (-(w * t)) * |D t| ≤
        c * sSup ((fun u : ℝ => Real.exp (-(w * u)) * |D u|) ''
          Ioc (0 : ℝ) R)) :
    ∀ t : ℝ, 0 < t → D t = 0 := by sorry
