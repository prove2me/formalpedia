-- Prove2me | Theorems.Thm_Apery_range_inner
-- name    : Apery.range_inner
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-12T14:21:53.959518+00:00
-- url     : https://prove2.me/theorems/42291527-b38b-4595-8dac-1e152612e6a4
-- title:
--   Growth, inner range $K/20 < p \le K/3$: exact table contribution $\le 0.04279K^2 + o(K^2)$
-- statement:
--   For every $\varepsilon > 0$ and all large $n$, the primes $K/20 < p \le K/3$ contribute at most
--
--   $$\sum_{K/20 < p \le K/3} c(k)\,\bigl(-L_k\bigr) \;\le\; \Bigl(\frac{322437603634266857629}{7535670527041937280000} + \varepsilon\Bigr) K^2, \qquad K = 40n,$$
--
--   i.e. $0.042788\ldots K^2$. In the source this is the composition of `range3_le` (`Apery/Growth/Assembly3.lean`) with the prime-sum limit `inner_psum_limit` (`Apery/Growth/Assembly4.lean`), absorbing the error term $10^8\theta(40n/3) \le \tfrac{16}{3}\cdot 10^9\,n$ with $\theta(y) \le 2y$. The constant is the exact evaluation `inner_integrals` of the piecewise-linear inner table (`Apery/Growth/InnerSum.lean`, `Apery/Growth/InnerTable.lean`; the exact table (5.18) of the paper). **Formalization Note** The weighted sum is written over integers $k$ with the weight `cPrime`; the range endpoints are the source's $2n$ and $40n/3$.
-- source:
--   https://github.com/mo271/Zeta5/blob/7fe736760f4b96bfdb4334b68e3b3124ecbe10b0/Apery/Growth/Assembly3.lean#L73-L121 + Apery/Growth/Assembly4.lean#L25-L35

import Mathlib
import Definitions.Def_Zeta5_SourceNorm
import Definitions.Def_Zeta5_SourcePrimeSum
import Definitions.Def_Zeta5_SourceConstants

open Finset Filter

namespace Apery

theorem range_inner : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
    ∑ k ∈ Ioc (2 * n) (40 * n / 3), cPrime k * (-(Lp n k : ℝ)) ≤
      (322437603634266857629 / 7535670527041937280000 + ε) * Kr n ^ 2 := by
  sorry

end Apery
