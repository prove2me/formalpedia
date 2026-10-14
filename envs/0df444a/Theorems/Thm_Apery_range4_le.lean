-- Prove2me | Theorems.Thm_Apery_range4_le
-- name    : Apery.range4_le
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-12T15:29:27.255451+00:00
-- url     : https://prove2.me/theorems/165b4088-6c42-4798-86ff-c67cbe84143c
-- title:
--   Outer range $K/3 < p \le 2h$: per-prime bounds summed to a prime sum $+\,10^5\theta(2h)$
-- statement:
--   For $n \ge 10400$, with $c(k) = \log k$ for primes and $0$ otherwise, $L_k$ the local exponent of the normaliser, $K = 40n$, $h = 37n$ and $\theta$ Chebyshev's function,
--
--   $$\sum_{K/3 < p \le 2h} c(k)\,\bigl(-L_k\bigr) \;\le\; \operatorname{psum} E_{\mathrm{out}}\,\frac{20}{37}\,3\,K \;+\; 10^5\,\theta(2h).$$
--
--   This is `range4_le` of `Apery/Growth/Assembly3.lean`: the per-prime outer point bounds `outer_Lp_le` (from `Apery/Growth/OuterPrime.lean`) and the additive errors `Cout_le` are summed over the range with `range_sum_le` and `big_prime_facts`. **Formalization Note** The statement is the source's; `psum`, `Eout`, `Lp`, `cPrime`, `Kr` are the platform definitions.
-- source:
--   https://github.com/mo271/Zeta5/blob/7fe736760f4b96bfdb4334b68e3b3124ecbe10b0/Apery/Growth/Assembly3.lean#L118-L145

import Mathlib
import Definitions.Def_Zeta5_SourceGrowth
import Definitions.Def_Zeta5_SourceGrowthTables
import Definitions.Def_Zeta5_SourcePrimeSum
import Definitions.Def_Zeta5_SourceConstants
import Definitions.Def_Zeta5_SourceNorm

open Finset

namespace Apery

/-- The outer prime range (`Apery/Growth/Assembly3.lean`). -/
lemma range4_le {n : ℕ} (hn : 10400 ≤ n) :
    ∑ k ∈ Ioc (40 * n / 3) (2 * (37 * n)), cPrime k * (-(Lp n k : ℝ)) ≤
      psum Eout (20 / 37) 3 (Kr n) + 10 ^ 5 * Chebyshev.theta (2 * (37 * n) : ℕ) := by
  sorry

end Apery
