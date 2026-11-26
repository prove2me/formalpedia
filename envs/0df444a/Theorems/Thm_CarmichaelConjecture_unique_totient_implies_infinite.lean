-- Prove2me | Theorems.Thm_CarmichaelConjecture_unique_totient_implies_infinite
-- name    : CarmichaelConjecture.unique_totient_implies_infinite
-- status  : Open
-- author  : @fangshuming
-- created : 2026-11-26T09:22:33.065648+00:00
-- url     : https://prove2.me/theorems/dcb1f6b3-fafa-51c0-8e6f-e74cf507f0a5
-- title:
--   One unique totient implies infinitely many
-- statement:
--   If there exists a natural number $m$ that is assumed exactly once as a value of Euler's totient function on the positive integers, then there are infinitely many such $m$. This is a known consequence of Ford's comparison of the counting functions $V_1(x)$ and $V(x)$ in The distribution of totients: a single multiplicity-one totient would in fact force a positive proportion of totients to have multiplicity one. The statement here asks only for infinitude.
-- source:
--   Kevin Ford, The distribution of totients, Ramanujan J. 2 (1998), 67–151, Theorem 2 (specialised to k=1) and the discussion in §1.3; 2012 revision, https://arxiv.org/abs/1104.3264

import Mathlib

namespace CarmichaelConjecture
theorem unique_totient_implies_infinite
    (h : ∃ m, ∃! n, 0 < n ∧ Nat.totient n = m) :
    {m : Nat | ∃! n, 0 < n ∧ Nat.totient n = m}.Infinite := by sorry
end CarmichaelConjecture
