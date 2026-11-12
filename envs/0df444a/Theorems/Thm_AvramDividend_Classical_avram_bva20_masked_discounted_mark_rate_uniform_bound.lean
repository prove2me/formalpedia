-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva20_masked_discounted_mark_rate_uniform_bound
-- name    : AvramDividend.Classical.avram_bva20_masked_discounted_mark_rate_uniform_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T20:27:47.916836+00:00
-- url     : https://prove2.me/theorems/401b54e0-c902-4bb5-9f1f-7c1f15b2b089
-- title:
--   Original closed-cap stopped discounted mark kernel inherits a uniform bound
-- statement:
--   When the original finite-activity negative-mark integrated gain is uniformly bounded by B throughout the actual inclusive reserve cap, its stopped discounted contribution has absolute value at most B at every nonnegative physical time, for nonnegative discount q. This supplies the explicit domination needed for both the original frozen-grid Riemann integrand and time-continuous compensated integrand in 7ccc2a1a. All ruin/cap masks are preserved exactly.
-- source:
--   Source-mask uniform domination for paired physical time measure DCT in original compensated K minus A convergence 7ccc2a1a.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bva20_masked_discounted_mark_rate_uniform_bound
    (C τ : ℝ≥0∞) (U : ℝ≥0 → ℝ) (ψ : ℝ → ℝ)
    (B q : ℝ) (hB : 0 ≤ B) (hq : 0 ≤ q)
    (hψ : ∀ b : ℝ, 0 ≤ b → ENNReal.ofReal b ≤ C → |ψ b| ≤ B)
    (t : ℝ≥0) :
    |if (t : ℝ≥0∞) < τ ∧
         0 ≤ U t ∧ ENNReal.ofReal (U t) ≤ C then
         Real.exp (-(q * (t : ℝ))) * ψ (U t)
       else 0| ≤ B := by sorry
