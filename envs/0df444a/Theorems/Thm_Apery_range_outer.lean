-- Prove2me | Theorems.Thm_Apery_range_outer
-- name    : Apery.range_outer
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-12T14:20:17.990899+00:00
-- url     : https://prove2.me/theorems/a5952f25-bd5d-4df1-9166-662e1097e388
-- title:
--   Growth, outer range $K/3 < p \le 2h$: outer table contribution $\le 1.34480K^2 + o(K^2)$
-- statement:
--   For every $\varepsilon > 0$ and all large $n$, the primes $K/3 < p \le 2h$ contribute at most
--
--   $$\sum_{K/3 < p \le 2h} c(k)\,\bigl(-L_k\bigr) \;\le\; \Bigl(\frac{129101}{96000} + \varepsilon\Bigr) K^2, \qquad K = 40n,\ h = 37n,$$
--
--   i.e. $1.344802\ldots K^2$. In the source this is the composition of `range4_le` (`Apery/Growth/Assembly3.lean`) with the prime-sum limit `outer_psum_limit` (`Apery/Growth/Assembly4.lean`), absorbing the error term $10^5\theta(2h) \le 148\cdot 10^5\,n$ with $\theta(y) \le 2y$. The constant is the evaluation `outer_integrals` of the piecewise-linear outer table (`Apery/Growth/OuterTable.lean`; the outer table of the paper). **Formalization Note** The weighted sum is written over integers $k$ with the weight `cPrime`; the range endpoints are the source's $40n/3$ and $2\cdot 37n$.
-- source:
--   https://github.com/mo271/Zeta5/blob/7fe736760f4b96bfdb4334b68e3b3124ecbe10b0/Apery/Growth/Assembly3.lean#L123-L144 + Apery/Growth/Assembly4.lean#L37-L49

import Mathlib
import Definitions.Def_Zeta5_SourceNorm
import Definitions.Def_Zeta5_SourcePrimeSum
import Definitions.Def_Zeta5_SourceConstants

open Finset Filter

namespace Apery

theorem range_outer : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
    ∑ k ∈ Ioc (40 * n / 3) (2 * (37 * n)), cPrime k * (-(Lp n k : ℝ)) ≤
      (129101 / 96000 + ε) * Kr n ^ 2 := by
  sorry

end Apery
