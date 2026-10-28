-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_exponential_tsum_untwist
-- name    : AvramDividend.Classical.causal_exponential_tsum_untwist
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T20:58:38.067285+00:00
-- url     : https://prove2.me/theorems/41d1ff1e-ff16-4683-a9da-a15ec6fc79bd
-- title:
--   Remove exponential damping from a real Gaussian Neumann infinite sum
-- statement:
--   Multiplying an infinite real Neumann sum of exp(-w x) weighted coefficients by exp(w x) yields the same infinite sum without the damping factor, for any fixed x and nonzero or zero scalar denominator a. This removes the only exponential prefactor in the explicit Gaussian C1 candidate and exposes its undamped Volterra series.
-- source:
--   Apply pinned Mathlib tsum_mul_left (valid even for nonsummable real families) to distribute the positive Esscher exponential over the infinite sum. The pointwise product exp(w x)exp(-w x)=1 cancels the two weights, leaving the exact primitive Neumann series for the C1 Gaussian derivative-resolvent candidate.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Tactic.Ring

open Real

theorem AvramDividend.Classical.causal_exponential_tsum_untwist
    (A : ℕ → ℝ) (w x a : ℝ) :
    Real.exp (w * x) *
      (∑' n : ℕ, (Real.exp (-w * x) * A n) / a) =
        (∑' n : ℕ, A n / a) := by sorry
