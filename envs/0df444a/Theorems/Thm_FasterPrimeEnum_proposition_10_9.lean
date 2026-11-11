-- Prove2me | Theorems.Thm_FasterPrimeEnum_proposition_10_9
-- name    : FasterPrimeEnum.proposition_10_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T10:39:53.243002+00:00
-- url     : https://prove2.me/theorems/d559a56c-cba5-4513-a033-cba714763b5d
-- title:
--   Proposition 10.9 — at most $O(N/\log^{13}N)$ rejected intervals
-- statement:
--   Let $N$ be large, let $A,\beta,T,R,Y$ be chosen as in Step 1 of the deterministic algorithm, so that $T=2^\beta\prod_{p\le A}p^2$ satisfies $\tfrac13(\log N)^{1/2}\log\log N<T<(\log N)^{1/2}\log\log N$, $R=13\log_2\log N+O(1)$ and $Y=\exp(40(\log N)^{1/2}\log\log N)+O(1)$, and let $T\mid N$. An interval $[rT,(r+1)T)$, $0\le r<N/T$, is rejected if it contains more than $R$ odd square-$Y$-rough integers or a square-prime that is not square-$Y$-rough. The number of rejected intervals is at most
--
--   $$
--   O\Big(\frac{N}{\log^{13}N}\Big).
--   $$
--
--   Only the rejected intervals need the slow direct test of Proposition 9.5, so this bound keeps that step within $O(N)$.
--
--   **Formalization Note** For every slack $c\ge0$ there are $K$ and $N_0$ such that for every $N\ge N_0$ and every choice meeting Step 1 with all $O(1)$ terms at most $c$, and with $T\mid N$, the count is at most $KN/(\log N)^{13}$.
--
--   Differences from the source:
--   - reading: parameters chosen in Step 1 as "= … + O(1)", and O(N/log^{13} N) for the large N of §10.2 → for every slack c ≥ 0, there are K and N₀ such that the bound holds for all N ≥ N₀ and all A, β, T, R, Y meeting Step 1 with every O(1) term at most c (Step1Params c); reason: Step 1 defines the parameters only up to O(1) and for large N; requiring the bound for every bounded slack is the strongest reading
--   - encoding: "Increasing N slightly if necessary, we may assume that T | N" → hypothesis T ∣ N; reason: the proposition is applied to the N after this adjustment
-- source:
--   Harvey, Faster enumeration of primes, arXiv:2606.22851 (held version, sha256 7fc13f17…), Proposition 10.9, p.102; §10.2 Step 1, p.101; Step 5, pp.101–102

import Mathlib
import Definitions.Def_FasterPrimeEnum_IsSquarePrime
import Definitions.Def_FasterPrimeEnum_IsRough
import Definitions.Def_FasterPrimeEnum_Rejected
import Definitions.Def_FasterPrimeEnum_Step1Params

set_option autoImplicit false

namespace FasterPrimeEnum

open Classical in
/-- **Proposition 10.9** — D. Harvey, *Faster enumeration of primes*, arXiv:2606.22851 (held version, sha256 7fc13f17…), p.102.

"The number of rejected intervals is at most O(N/log^{13} N)."

The intervals are `[rT, (r+1)T)` for `0 ⩽ r < N/T`, and the parameters `T, R, Y` are those of
Step 1 (p.101), with `T | N`.

**Formalization Note.** "= … + O(1)" in Step 1 is read with a uniform slack: for every `c ⩾ 0`
there are `K` and `N₀` such that, for every `N ⩾ N₀` and every choice of `A, β, T, R, Y` meeting
Step 1 with all `O(1)` terms at most `c` (`Step1Params c`) and with `T | N`, the number of rejected
intervals is at most `K N/(log N)^{13}`. The special form `T = 2^β ∏_{p⩽A} p²` is kept
(Remark 10.8). -/
theorem proposition_10_9 :
    ∀ c : ℝ, 0 ≤ c → ∃ K : ℝ, ∃ N₀ : ℕ,
      ∀ N A β T R Y : ℕ, N₀ ≤ N → Step1Params c N A β T R Y → T ∣ N →
        ((((Finset.range (N / T)).filter fun r => Rejected T R Y r).card : ℕ) : ℝ) ≤
          K * N / Real.log (N : ℝ) ^ 13 := by sorry

end FasterPrimeEnum
