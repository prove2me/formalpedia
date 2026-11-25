-- Prove2me | Theorems.Thm_DetDLP_m89_prime_predecessor_factor_oracle
-- name    : DetDLP.m89_prime_predecessor_factor_oracle
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-23T17:32:28.166139+00:00
-- url     : https://prove2.me/theorems/9e9f3326-30d3-4467-b65e-d7df112a5e7f
-- title:
--   Factoring a prime predecessor with an explicit exceptional branch
-- statement:
--   Let $A$ list the prime factors of every $N\ge 2$ with bounds $T(N),S(N)$. The wrapper computes the encoded factor list of $p-1$ from the canonical binary word of a prime $p$. For odd primes its bounds are $T(p-1)+1$ and $S(p-1)$; for $p=2$ they are $5$ steps and at most $13$ cells per tape in aggregate (space bound $13$ times the tape count).
-- source:
--   S. Liu, B. Zhang and K. Ren, A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem, Zhejiang University preprint, 23 November 2026, Proposition 3.3 and its proof, Section 3.3.

import Definitions.Def_DetDLP_Machine
open DetDLP OAI.Algorithms.SubexponentialSAT.Computation OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

theorem DetDLP.m89_prime_predecessor_factor_oracle (A : PrimitiveMachine) (o : Fin A.tapeCount) (T S : ℕ → ℝ)
    (hf : ∀ N : ℕ, 2 ≤ N → RunsWithin A o (countWord N) (encodeNatListBin N.primeFactorsList) (T N) (S N)) :
    ∃ (M : PrimitiveMachine) (out : Fin M.tapeCount), ∀ (p : ℕ), p.Prime →
      RunsWithin M out (countWord p) (encodeNatListBin (p-1).primeFactorsList)
        (if p = 2 then 5 else T (p-1)+1) (if p = 2 then (13*A.tapeCount : ℕ) else S (p-1)) := by sorry
