-- Prove2me | Theorems.Thm_DerivativeChainPrivate_finite_structured_core_completion
-- name    : DerivativeChainPrivate.finite_structured_core_completion
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-26T20:12:23.233824+00:00
-- url     : https://prove2.me/theorems/060a6cb8-7901-4b04-b71c-152366dbbae8
-- title:
--   Finite probability and energy completion with explicit hypotheses
-- statement:
--   For a finite nonnegative probability law, suppose centered increments are orthogonal in expectation, terminal points have mean u and lie in the unit disk, and every positive-mass path satisfies the stated squared-length energy bound. A positive-mass path then has length at most sqrt((s+1)(1-normSq(u))). The orthogonality, mean, disk and pathwise hypotheses are assumptions; no polynomial-root construction or unrestricted chain theorem is asserted.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/52c50aeb6d4adf24f4ae03d555d1181eae370084/results/verified-supporting-lemmas-20261017/finite/Solution.lean#L11-L127

import Mathlib
namespace DerivativeChainPrivate
end DerivativeChainPrivate
open DerivativeChainPrivate Filter Topology Polynomial
open scoped BigOperators
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

theorem DerivativeChainPrivate.finite_structured_core_completion {Ω : Type*} [Fintype Ω]
    (π length : Ω → ℝ) (X : ℕ → Ω → ℂ) (s : ℕ) (u : ℂ)
    (hπ : ∀ ω, 0 ≤ π ω) (htotal : ∑ ω, π ω = 1)
    (horth : ∀ k < s, ∑ ω, π ω *
      ((X k ω - u).re * (X (k + 1) ω - X k ω).re +
        (X k ω - u).im * (X (k + 1) ω - X k ω).im) = 0)
    (hmean_re : ∑ ω, π ω * (X s ω).re = u.re)
    (hmean_im : ∑ ω, π ω * (X s ω).im = u.im)
    (hdisk : ∀ ω, 0 < π ω → Complex.normSq (X s ω) ≤ 1)
    (hpoint : ∀ ω, 0 < π ω → length ω ^ 2 ≤ ((s : ℝ) + 1) *
      (Complex.normSq (X 0 ω - u) +
        ∑ k ∈ Finset.range s, Complex.normSq (X (k + 1) ω - X k ω))) :
    ∃ ω, 0 < π ω ∧
      length ω ≤ Real.sqrt (((s : ℝ) + 1) * (1 - Complex.normSq u)) := by sorry
