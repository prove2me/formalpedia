-- Prove2me | Theorems.Thm_Apery_small_range_le
-- name    : Apery.small_range_le
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-12T14:21:49.068505+00:00
-- url     : https://prove2.me/theorems/45f5ac5b-fe93-4e7e-94a6-452230330765
-- title:
--   Growth, small primes $p \le K/400$: bound by Chebyshev's $\theta$
-- statement:
--   For $n \ge 1$ the small primes $k \le n/10$ (i.e. $p \le K/400$) satisfy
--
--   $$\sum_{k \le n/10} c(k)\,\bigl(-L_k\bigr) \;\le\; 6\cdot 37n\,\Bigl(\theta\bigl(\tfrac{n}{10}\bigr) + \bigl(\sqrt{200n}+1\bigr)\log(200n)\Bigr) + 37n \cdot 100,$$
--
--   where $\theta$ is Chebyshev's function, $c(k) = \log k$ for primes and $0$ otherwise, and $L_k$ is the small-prime exponent (3.12). This is the source's `small_range_le` (`Apery/Growth/Assembly1.lean`), proved there from the definition of `cPrime`, $\theta(M) \le \sum_{k \le M} c(k)$ and elementary counts ($\#\{k : k^2 \le 200n\} \le \sqrt{200n}+1$, $\#\{k \le 24\} = 24$). Combined with the prime number theorem $\theta(y) \sim y$ it produces the small-prime contribution $22.2/1600\cdot K^2 + o(K^2)$ of Proposition 5.2. **Formalization Note** The statement is the source's; it is independent of the prime number theorem.
-- source:
--   https://github.com/mo271/Zeta5/blob/7fe736760f4b96bfdb4334b68e3b3124ecbe10b0/Apery/Growth/Assembly1.lean#L82-L163

import Mathlib
import Definitions.Def_Zeta5_SourceNorm
import Definitions.Def_Zeta5_SourcePrimeSum

open Finset

namespace Apery

lemma small_range_le (n : ℕ) (hn : 1 ≤ n) :
    ∑ k ∈ Ioc 0 (n / 10), cPrime k * (-(Lp n k : ℝ)) ≤
      6 * (37 * n) * (Chebyshev.theta (n / 10 : ℕ) + (Real.sqrt (200 * n) + 1) * Real.log (200 * n)) +
        (37 * n) * 100 := by
  sorry

end Apery
