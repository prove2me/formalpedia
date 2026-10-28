-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_neumann_constant_head_tsum
-- name    : AvramDividend.Classical.causal_neumann_constant_head_tsum
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T22:02:14.032451+00:00
-- url     : https://prove2.me/theorems/cd3aa5b9-fd43-45ca-aebd-e717128b39a2
-- title:
--   Gaussian Neumann series with its constant head equals the full correction sum
-- statement:
--   If a summable family of Gaussian Neumann corrections starts with the constant 1/a and its subsequent terms equal H_n, then the C1 candidate g defined as 1/a plus the H_n series is exactly the full sum of corrections. This identifies the function to which the resolvent finite sums converge.
-- source:
--   Mathlib Summable.tsum_eq_zero_add identifies a summable series with its zeroth term plus the shifted tail. Gaussian C1 Neumann data has Q0=1/a and Q(n+1) the untwisted primitive Hn. Combine this with causal_exponential_tsum_untwist to obtain the exact g=tsum Q equality required by causal_neumann_tsum_partial_sum_tendsto.

import Mathlib.Data.Real.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

theorem AvramDividend.Classical.causal_neumann_constant_head_tsum
    (Q H : ℕ → ℝ → ℝ) (a : ℝ) (g : ℝ → ℝ)
    (hQ : ∀ x : ℝ, Summable (fun n : ℕ => Q n x))
    (hQ0 : Q 0 = fun _ : ℝ => 1 / a)
    (hQsucc : ∀ n : ℕ, Q (n + 1) = H n)
    (hg : ∀ x : ℝ, g x = 1 / a + ∑' n : ℕ, H n x) :
    ∀ x : ℝ, g x = ∑' n : ℕ, Q n x := by sorry
