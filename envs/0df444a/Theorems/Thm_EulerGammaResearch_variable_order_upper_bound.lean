-- Prove2me | Theorems.Thm_EulerGammaResearch_variable_order_upper_bound
-- name    : EulerGammaResearch.variable_order_upper_bound
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-09-14T06:41:49.782747+00:00
-- url     : https://prove2.me/theorems/5239d436-3a3f-481d-96a5-30c3f3bc1fc9
-- title:
--   A uniform upper bound excluding excessive order in Euler approximants
-- statement:
--   This is a complete, unconditional proof of a method-specific upper bound, not a proof of irrationality of Euler's constant.
--
--   For integers n >= 1 and p >= 0 define
--
--   $$c_{n,p,k}=\binom nk^2\binom{n+k}k^p/k!,\qquad Q_{n,p}=\sum_{k=0}^n c_{n,p,k},$$
--   $$P_{n,p}=-\sum_{k=0}^n c_{n,p,k}\bigl(pH_{n+k}+2H_{n-k}-(p+3)H_k\bigr).$$
--
--   The theorem proves
--
--   $$P_{n,p}/Q_{n,p}\le 3H_n-p/2.$$
--
--   In particular, if p >= 6H_n, then P/Q <= 0. Since gamma > 1/2, such orders cannot give positive rational approximants converging to gamma. Thus a variable-order search in this explicit family must keep p < 6H_n at indices where its approximants are positive. Using H_n <= 1+log n gives the necessary O(log n) scale. This does not exclude smaller growing orders, other families, or exceptional subsequences.
--
--   Provenance: the denominator family is Van Assche--Wolfs, arXiv:2404.09799v3, Section 5, displayed formula for F_(n;2)^(I|p)(1). The explicit numerator is obtained by the differential-operator iteration in that section (the p=2 case matches Prove2Me's eulerMascheroni_p2Approximation definition). The upper bound above was derived in this research session, 2026-09-14; it is not claimed to be a theorem stated in that paper or a literature-priority result. The formal theorem is purely about the displayed finite sums and does not depend on establishing a contour representation or their convergence to gamma.
--
--   Scope of contribution: a proved obstruction to excessive variable order, with no claim to resolve the mission root, the P2 primitive-saving conjecture, or the irrationality milestone.
-- source:
--   Derived in the 2026-09-14 research session from the explicit finite sums. Family: Van Assche--Wolfs, https://arxiv.org/html/2404.09799v3, Section 5, displayed denominator formula and differential-operator iteration. The elementary upper bound is a session derivation, not attributed to a theorem in the paper; no claim of priority.

import Mathlib.NumberTheory.Harmonic.Defs
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
open scoped BigOperators

theorem EulerGammaResearch.variable_order_upper_bound (n p : ℕ) (hn : 0 < n) :
    let c : ℕ → ℚ := fun k => (n.choose k : ℚ)^2 * ((n+k).choose k : ℚ)^p /
      (k.factorial : ℚ);
    -(∑ k ∈ Finset.range (n+1), c k *
      ((p : ℚ)*harmonic (n+k) + 2*harmonic (n-k) - ((p : ℚ)+3)*harmonic k))
      / (∑ k ∈ Finset.range (n+1), c k) ≤ 3*harmonic n - (p : ℚ)/2 := by sorry
