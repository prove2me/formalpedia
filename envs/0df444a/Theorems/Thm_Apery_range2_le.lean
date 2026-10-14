-- Prove2me | Theorems.Thm_Apery_range2_le
-- name    : Apery.range2_le
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-12T14:45:55.61889+00:00
-- url     : https://prove2.me/theorems/ae7a188e-a771-45a3-a372-f6392d268ae7
-- title:
--   Tail range $K/400 < p \le K/20$: per-prime bounds summed to a prime sum $+\,10^7\theta(2n)$
-- statement:
--   For $n \ge 10400$, with $c(k) = \log k$ for primes and $0$ otherwise, $L_k$ the local exponent of the normaliser, $K = 40n$ and $\theta$ Chebyshev's function,
--
--   $$\sum_{K/400 < p \le K/20} c(k)\,\bigl(-L_k\bigr) \;\le\; \operatorname{psum}\Bigl(xF(x) + \frac{27}{16}\Bigr)\,20\,400\,K \;+\; 10^7\,\theta(2n).$$
--
--   This is `range2_le` of `Apery/Growth/Assembly3.lean`: the per-prime point bounds `tail_Lp_le` (from `Apery/Growth/TailPrime.lean`, obtained from the inner bound `inner_Lp_le` of `Apery/Growth/InnerPrime.lean`) and the additive error `Ctail_le` are summed over the range with `range_sum_le` and `big_prime_facts`. **Formalization Note** The statement is the source's; `psum`, `Ftail`, `Lp`, `cPrime`, `Kr` are the platform definitions.
-- source:
--   https://github.com/mo271/Zeta5/blob/7fe736760f4b96bfdb4334b68e3b3124ecbe10b0/Apery/Growth/Assembly3.lean#L49-L71

import Mathlib
import Definitions.Def_Zeta5_SourceGrowth
import Definitions.Def_Zeta5_SourcePrimeSum
import Definitions.Def_Zeta5_SourceConstants
import Definitions.Def_Zeta5_SourceNorm

open Finset

namespace Apery

/-- The inner tail range (`Apery/Growth/Assembly3.lean`). -/
lemma range2_le {n : ℕ} (hn : 10400 ≤ n) :
    ∑ k ∈ Ioc (n / 10) (2 * n), cPrime k * (-(Lp n k : ℝ)) ≤
      psum (fun x => x * Ftail x + 27 / 16) 20 400 (Kr n) + 10 ^ 7 * Chebyshev.theta (2 * n : ℕ) := by
  sorry

end Apery
