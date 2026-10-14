-- Prove2me | Theorems.Thm_Apery_range3_le
-- name    : Apery.range3_le
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-12T15:29:24.460654+00:00
-- url     : https://prove2.me/theorems/a0f40938-7b41-4fcb-b006-3b6d8134af0d
-- title:
--   Inner range $K/20 < p \le K/3$: per-prime bounds summed to a prime sum $+\,10^8\theta(40n/3)$
-- statement:
--   For $n \ge 10400$, with $c(k) = \log k$ for primes and $0$ otherwise, $L_k$ the local exponent of the normaliser, $K = 40n$ and $\theta$ Chebyshev's function,
--
--   $$\sum_{K/20 < p \le K/3} c(k)\,\bigl(-L_k\bigr) \;\le\; \operatorname{psum} F_{\mathrm{in}}\,3\,20\,K \;+\; 10^8\,\theta\Bigl(\Bigl\lfloor\frac{40n}{3}\Bigr\rfloor\Bigr).$$
--
--   This is `range3_le` of `Apery/Growth/Assembly3.lean`: the per-prime inner point bounds `table_Lp_le` (from `Apery/Growth/TablePrime.lean`, via the discrete bound `inner_Lp_le` and the table piece `inner_table_k`), the additive errors `Ctab_le`, the piecewise table equality `inner_table` and then `range_sum_le` with `big_prime_facts`. **Formalization Note** The statement is the source's; `psum`, `fIn`, `Lp`, `cPrime`, `Kr` are the platform definitions.
-- source:
--   https://github.com/mo271/Zeta5/blob/7fe736760f4b96bfdb4334b68e3b3124ecbe10b0/Apery/Growth/Assembly3.lean#L84-L115

import Mathlib
import Definitions.Def_Zeta5_SourceGrowth
import Definitions.Def_Zeta5_SourceGrowthTables
import Definitions.Def_Zeta5_SourcePrimeSum
import Definitions.Def_Zeta5_SourceConstants
import Definitions.Def_Zeta5_SourceNorm

open Finset

namespace Apery

/-- The inner prime range (`Apery/Growth/Assembly3.lean`). -/
lemma range3_le {n : ℕ} (hn : 10400 ≤ n) :
    ∑ k ∈ Ioc (2 * n) (40 * n / 3), cPrime k * (-(Lp n k : ℝ)) ≤
      psum fIn 3 20 (Kr n) + 10 ^ 8 * Chebyshev.theta (40 * n / 3 : ℕ) := by
  sorry

end Apery
