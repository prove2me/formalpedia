-- Prove2me | Theorems.Thm_CachonCoord_Proportional_p52_what_above_cost
-- name    : CachonCoord.Proportional.p52_what_above_cost
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T04:44:26.342983+00:00
-- url     : https://prove2.me/theorems/a094a8ef-534d-4bca-bcd6-fa6a8c15d08a
-- title:
--   p. 52 — ŵ(q°) > c when n > 1, so the supplier earns a positive profit with the coordinating wholesale price
-- statement:
--   Let $n \ge 2$ and let $q^o$ solve (20), $F(q^o) = (p-c)/p$. The coordinating wholesale price exceeds the production cost,
--
--   $$
--   \widehat w(q^o) > c,
--   $$
--
--   and the supplier's profit $q^o\big(\widehat w(q^o) - c\big)$ under that contract is positive.
--
--   With a single retailer, coordination by a wholesale price requires marginal-cost pricing; with competing retailers the demand-stealing effect lets the supplier coordinate and earn a profit.
--
--   **Formalization Note** The page writes "Given that $F(q^o) = (p-c)/c$"; (20) has $(p-c)/p$, which is used. The hypotheses on the demand law are the chapter's standing assumptions (p. 7), carried by the model.
-- source:
--   Cachon (2003), Supply Chain Coordination with Contracts, 3rd draft (Jan. 2003), §6.5.1, p. 52 ("it can be shown that ŵ(q°) > c when n > 1"; printed slip F(q°) = (p − c)/c)

import Mathlib
import Definitions.Def_CachonCoord_Proportional_Demand
import Definitions.Def_CachonCoord_Proportional_Nash
import Definitions.Def_CachonCoord_Proportional_Game

namespace CachonCoord.Proportional

/-- p. 52: with `F(q°) = (p − c)/p` (the page prints `(p − c)/c`) and `(1/q)∫_0^q F < F(q)`,
"it can be shown that `ŵ(q°) > c` when `n > 1`. Hence, the supplier earns a positive profit with
that coordinating contract." -/
theorem p52_what_above_cost (M : Model) (n : ℕ) (hn : 2 ≤ n) (qo : ℝ)
    (hqo : M.F qo = (M.p - M.c) / M.p) :
    M.c < M.what n qo ∧ 0 < M.supplierProfit (M.what n qo) 0 qo := by sorry

end CachonCoord.Proportional
