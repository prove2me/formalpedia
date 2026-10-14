-- Prove2me | Theorems.Thm_Apery_low_order
-- name    : Apery.low_order
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-12T14:20:11.193762+00:00
-- url     : https://prove2.me/theorems/44e6817b-ef83-49b2-88d9-5c20c486f2c8
-- title:
--   Growth: the lower-order terms are $o(K^2)$
-- statement:
--   For every $\delta > 0$ and all large $n$,
--
--   $$6\cdot 37n\,\bigl(\sqrt{200n}+1\bigr)\log(200n) + 3\cdot 10^9\,n \;\le\; \delta\,K^2, \qquad K = 40n.$$
--
--   This is the source's `low_order` (`Apery/Growth.lean`). It absorbs the elementary error terms of the four prime ranges of the growth estimate for the normaliser: the square-root counting term $6\cdot 37n(\sqrt{200n}+1)\log(200n)$ and the $100\cdot 37n$ of the small range, together with the $\theta \le 2y$ errors $4\cdot 10^7 n$, $\tfrac{16}{3}\cdot 10^9 n$, $1.48\cdot 10^7 n$ of the remaining ranges, all below $3\cdot 10^9 n$. **Formalization Note** The statement is the source's; it is independent of the prime number theorem.
-- source:
--   https://github.com/mo271/Zeta5/blob/7fe736760f4b96bfdb4334b68e3b3124ecbe10b0/Apery/Growth.lean#L24-L62

import Mathlib
import Definitions.Def_Zeta5_SourceConstants

open Filter

namespace Apery

lemma low_order {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, 6 * (37 * (n : ℝ)) * ((Real.sqrt (200 * n) + 1) * Real.log (200 * n)) +
      3 * 10 ^ 9 * n ≤ δ * Kr n ^ 2 := by
  sorry

end Apery
