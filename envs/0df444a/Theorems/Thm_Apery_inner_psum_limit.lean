-- Prove2me | Theorems.Thm_Apery_inner_psum_limit
-- name    : Apery.inner_psum_limit
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-12T15:30:36.442583+00:00
-- url     : https://prove2.me/theorems/4f8a264a-7097-4dea-9ad4-923e305672da
-- title:
--   Inner table sum: $\mathrm{psum}\,F_{\mathrm{in}}\,3\,20\,K/K^2 \le 322437603634266857629/7535670527041937280000 + \delta$
-- statement:
--   For every $\delta > 0$ and all sufficiently large real $K$,
--
--   $$\frac{1}{K^2}\sum_{K/20 < p \le K/3} p\,F_{\mathrm{in}}\Bigl(\frac{K}{p}\Bigr)\log p \;\le\; \frac{322437603634266857629}{7535670527041937280000} + \delta,$$
--
--   i.e. the inner prime sum is at most $0.042788\ldots K^2 + o(K^2)$, where $F_{\mathrm{in}}(x) = g_{\mathrm{in}}(\mathrm{pieceIdx}\,t_{\mathrm{in}}\,125\,x, x)$ is the 125-piece inner table of `Apery/Growth/InnerSum.lean`. This is `inner_psum_limit` of `Apery/Growth/Assembly4.lean`, obtained from `psum_piecewise_le` (Abel summation + the prime number theorem), the piecewise table equality `inner_table` and the numerical evaluation `inner_integrals` of `Apery/Growth/TableIntegrals.lean`. **Formalization Note** The statement is the source's; `psum` and `fIn` are the platform definitions.
-- source:
--   https://github.com/mo271/Zeta5/blob/7fe736760f4b96bfdb4334b68e3b3124ecbe10b0/Apery/Growth/Assembly4.lean#L26-L39

import Mathlib
import Definitions.Def_Zeta5_SourceGrowth
import Definitions.Def_Zeta5_SourceGrowthTables

open Finset Filter

namespace Apery

/-- The inner table sum (`Apery/Growth/Assembly4.lean`). -/
lemma inner_psum_limit {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ K : ℝ in atTop, psum fIn 3 20 K / K ^ 2 ≤
      322437603634266857629 / 7535670527041937280000 + δ := by
  sorry

end Apery
