-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_05_gaussian_exponential_derivative_cancel
-- name    : AvramDividend.Classical.avram_wave3_05_gaussian_exponential_derivative_cancel
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T00:01:43.853992+00:00
-- url     : https://prove2.me/theorems/52d8abcb-7c5d-49e0-a025-142b6ad10bf5
-- title:
--   Exact derivative of Gaussian exponential Neumann resolvent from signed density
-- statement:
--   When Gaussian damped primitives H_n have termwise derivatives H'_n=P_n/a-wH_n and both power and primitive series converge pointwise, differentiate the native source resolvent g=1/a+exp(wx)∑H_n and cancel the w terms. The result is the precise derivative g'(x)=exp(wx)/a∑P_n(x) at every positive x. This is a necessary algebraic bridge from signed-density L1 to weighted Gaussian scale-function W'' L1.
-- source:
--   Gaussian antitone Volterra construction and pinned Mathlib HasDerivAt.mul, tsum_sub, tsum_div_const, tsum_mul_left.

import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Tactic.Ring

open Set

theorem AvramDividend.Classical.avram_wave3_05_gaussian_exponential_derivative_cancel
    (P H : ℕ → ℝ → ℝ) (a w : ℝ)
    (hSeries : ∀ x : ℝ, 0 < x →
      HasDerivAt (fun z : ℝ => ∑' n : ℕ, H n z)
        (∑' n : ℕ, (P n x / a - w * H n x)) x)
    (hPsum : ∀ x : ℝ, 0 < x → Summable (fun n : ℕ => P n x))
    (hHsum : ∀ x : ℝ, 0 < x → Summable (fun n : ℕ => H n x)) :
    ∀ x : ℝ, 0 < x →
      HasDerivAt
        (fun z : ℝ => 1 / a + Real.exp (w * z) *
          (∑' n : ℕ, H n z))
        (Real.exp (w * x) * ((∑' n : ℕ, P n x) / a)) x := by sorry
