-- Prove2me | Theorems.Thm_CarmichaelConjecture_ford_multiplicity_bound
-- name    : CarmichaelConjecture.ford_multiplicity_bound
-- status  : Open
-- author  : @fangshuming
-- created : 2026-11-26T09:22:30.670371+00:00
-- url     : https://prove2.me/theorems/a3031445-9fad-5268-9b2b-f171990d4b4d
-- title:
--   If $A(m)=1$, then $m\ge 10^{10^{10}}$
-- statement:
--   Let $m$ be a natural number for which there exists a unique positive integer $n$ with $\varphi(n)=m$. Then $m\ge 10^{10^{10}}$. This is a known theorem of Ford (Theorem 6 in The distribution of totients). The bound is on the totient value $m$, and therefore also forces any unique positive preimage to exceed $10^{10^{10}}$.
-- source:
--   Kevin Ford, The distribution of totients, Ramanujan J. 2 (1998), 67–151, Theorem 6; 2012 revision, https://arxiv.org/abs/1104.3264

import Mathlib

namespace CarmichaelConjecture
theorem ford_multiplicity_bound {m : Nat}
    (h : ∃! n, 0 < n ∧ Nat.totient n = m) :
    10 ^ (10 ^ 10) ≤ m := by sorry
end CarmichaelConjecture
