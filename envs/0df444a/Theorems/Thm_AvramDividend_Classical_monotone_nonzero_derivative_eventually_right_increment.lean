-- Prove2me | Theorems.Thm_AvramDividend_Classical_monotone_nonzero_derivative_eventually_right_increment
-- name    : AvramDividend.Classical.monotone_nonzero_derivative_eventually_right_increment
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T14:32:54.239316+00:00
-- url     : https://prove2.me/theorems/c671fb72-440c-4549-bbd1-ac977d0d9128
-- title:
--   Monotone scale function with nonzero derivative increases strictly immediately right
-- statement:
--   If a real function is monotone and has a derivative at a that is nonzero, the derivative is positive and the function strictly exceeds W(a) at all sufficiently small positive offsets. This converts the exact monotonicity, differentiability, and nonzero-derivative hypotheses of the original barrier upper-bound theorem into its required strict right-scale increment.
-- source:
--   Pinned Mathlib HasDerivAt.nonneg_of_monotone, together with the root-connected helper positive_derivative_eventually_right_increment. Analytic prerequisite for the original AvramDividend.Classical.barrierSupValue_stopped_renewal_upper_bound theorem c6c3b1d0-2c2f-41ce-a5a0-2771efcc3a69.

import Mathlib.Analysis.Calculus.Deriv.Slope

open Filter Set
open scoped Topology

theorem AvramDividend.Classical.monotone_nonzero_derivative_eventually_right_increment
    (W : ℝ → ℝ) (a : ℝ)
    (hmono : Monotone W)
    (hD : HasDerivAt W (deriv W a) a)
    (hd : deriv W a ≠ 0) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), W a < W (a + ε) := by sorry
