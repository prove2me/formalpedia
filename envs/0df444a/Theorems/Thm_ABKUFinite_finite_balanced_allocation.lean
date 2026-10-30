-- Prove2me | Theorems.Thm_ABKUFinite_finite_balanced_allocation
-- name    : ABKUFinite.finite_balanced_allocation
-- status  : Open
-- author  : @Yuxuan Xu
-- created : 2026-10-29T10:33:33.050392+00:00
-- url     : https://prove2.me/theorems/d5c1a87e-6c15-4a5a-a9fb-b2f563f23557
-- title:
--   Finite equal-load theorem — two-sided bound
-- statement:
--   For every natural number \(d\), there exists a nonnegative real \(C\) such that for every positive real \(\varepsilon\), there exists a natural number \(N\) such that, for every natural number \(n\ge N\), the uniform probability that the maximum load differs from \(\log\log(n+1)/\log(d+2)\) by at most \(C\) is at least \(1-\varepsilon\). The process allocates \(n+1\) balls sequentially to \(n+1\) initially empty bins, each ball making \(d+2\) independent uniform choices with replacement and joining the earliest minimum-load choice. The constant \(C\) may depend on \(d\) but not on \(\varepsilon\) or \(n\); \(N\) may depend on \(d\) and \(\varepsilon\).
-- source:
--   Azar, Broder, Karlin, Upfal (1999), Balanced Allocations, https://cs.brown.edu/people/eupfal/papers/SICOMP29.pdf, p.181; Theorems 3.2 and 3.3 combined; equal-load clause of Theorem 1.1

import Definitions.Def_ABKUFinite_Model

namespace ABKUFinite
theorem finite_balanced_allocation (d : ℕ) : TwoSided d := by sorry
end ABKUFinite
