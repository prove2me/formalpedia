-- Prove2me | Theorems.Thm_Apery_range_tail
-- name    : Apery.range_tail
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-12T14:20:26.492588+00:00
-- url     : https://prove2.me/theorems/4821419e-98f3-4e07-a013-ad744e625b3a
-- title:
--   Growth, tail range $K/400 < p \le K/20$: contribution $\le -0.05346K^2 + o(K^2)$
-- statement:
--   With $c(k) = \log k$ for primes and $0$ otherwise, and $L_k$ the local exponent of the normaliser: for every $\varepsilon > 0$ and all large $n$, the primes $K/400 < p \le K/20$ contribute at most
--
--   $$\sum_{K/400 < p \le K/20} c(k)\,\bigl(-L_k\bigr) \;\le\; \Bigl(-\frac{6843153}{128000000} + \varepsilon\Bigr) K^2, \qquad K = 40n,$$
--
--   i.e. $-0.0534621\ldots K^2$. In the source this is the composition of `range2_le` (`Apery/Growth/Assembly3.lean`) with the prime-sum limit `tail_psum_limit` (`Apery/Growth/Assembly4.lean`, via `psum_piecewise_le` and the Abel summation of `Apery/PrimeSum.lean`), absorbing the error term $10^7\theta(2n) \le 4\cdot 10^7n$ with $\theta(y) \le 2y$; the constant is evaluated by the table `Apery/Growth/TailPrime.lean` (`tail_sum_le`). **Formalization Note** The weighted sum is written over integers $k$ with the weight `cPrime`; the range endpoints are the source's $n/10$ and $2n$.
-- source:
--   https://github.com/mo271/Zeta5/blob/7fe736760f4b96bfdb4334b68e3b3124ecbe10b0/Apery/Growth/Assembly3.lean#L49-L71 + Apery/Growth/Assembly4.lean#L63-L94

import Mathlib
import Definitions.Def_Zeta5_SourceNorm
import Definitions.Def_Zeta5_SourcePrimeSum
import Definitions.Def_Zeta5_SourceConstants

open Finset Filter

namespace Apery

theorem range_tail : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
    ∑ k ∈ Ioc (n / 10) (2 * n), cPrime k * (-(Lp n k : ℝ)) ≤
      (-6843153 / 128000000 + ε) * Kr n ^ 2 := by
  sorry

end Apery
