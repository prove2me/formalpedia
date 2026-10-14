-- Prove2me | Theorems.Thm_Apery_outer_psum_limit
-- name    : Apery.outer_psum_limit
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-12T15:29:34.588786+00:00
-- url     : https://prove2.me/theorems/92637176-8e91-49e2-911a-6a08c840df87
-- title:
--   Outer table sum: $\mathrm{psum}\,E_{\mathrm{out}}\,20/37\,3\,K/K^2 \le 129101/96000 + \delta$
-- statement:
--   For every $\delta > 0$ and all sufficiently large real $K$,
--
--   $$\frac{1}{K^2}\sum_{K/3 < p \le 37K/20} p\,E_{\mathrm{out}}\Bigl(\frac{K}{p}\Bigr)\log p \;\le\; \frac{129101}{96000} + \delta,$$
--
--   i.e. the outer prime sum is at most $1.34480\ldots K^2 + o(K^2)$. This is `outer_psum_limit` of `Apery/Growth/Assembly4.lean`, obtained from the piecewise-linear majorant `tOut`/`gOut` on the 13-piece grid on $[20/37, 3]$ via `psum_piecewise_le` (Abel summation + the prime number theorem) and the numerical evaluation `outer_integrals` of `Apery/Growth/TableIntegrals.lean`. **Formalization Note** The statement is the source's; `psum` and `Eout` are the platform definitions.
-- source:
--   https://github.com/mo271/Zeta5/blob/7fe736760f4b96bfdb4334b68e3b3124ecbe10b0/Apery/Growth/Assembly4.lean#L41-L50

import Mathlib
import Definitions.Def_Zeta5_SourceGrowth
import Definitions.Def_Zeta5_SourceGrowthTables

open Finset Filter

namespace Apery

/-- The outer table sum (`Apery/Growth/Assembly4.lean`). -/
lemma outer_psum_limit {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ K : ℝ in atTop, psum Eout (20 / 37) 3 K / K ^ 2 ≤ 129101 / 96000 + δ := by
  sorry

end Apery
