-- Prove2me | Theorems.Thm_CachonCoord_Proportional_p53_lower_bound_ratio
-- name    : CachonCoord.Proportional.p53_lower_bound_ratio
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T04:44:47.700771+00:00
-- url     : https://prove2.me/theorems/db64a0af-a7f3-4b36-8e0a-886c75c1ea01
-- title:
--   p. 53 — π_s(q°, w_b(0), 0)/Π(q°) = (n − 1)/n
-- statement:
--   Let $n \ge 2$ and let $q^o$ solve (20). The optimal chain profit is positive, $\Pi(q^o) > 0$, and the coordinating contract with $b = 0$ (the coordinating wholesale-price contract) gives the supplier the share
--
--   $$
--   \frac{\pi_s(q^o, w_b(0), 0)}{\Pi(q^o)} = \frac{n-1}{n}
--   $$
--
--   of it. This is a lower bound on what the supplier earns with her optimal wholesale price, so the gain from a coordinating buy-back over the best wholesale price shrinks as $n$ grows.
--
--   **Formalization Note** The supplier's profit is computed from the transfers, $w_b(0)q^o - cq^o$. The hypotheses on the demand law are the chapter's standing assumptions (p. 7), carried by the model.
-- source:
--   Cachon (2003), Supply Chain Coordination with Contracts, 3rd draft (Jan. 2003), §6.5.1, p. 53 (the ratio display)

import Mathlib
import Definitions.Def_CachonCoord_Proportional_Demand
import Definitions.Def_CachonCoord_Proportional_Nash
import Definitions.Def_CachonCoord_Proportional_Game

namespace CachonCoord.Proportional

/-- p. 53: the coordinating contract with `b = 0` gives the supplier the share `(n − 1)/n` of the
optimal supply chain profit, `π_s(q°, w_b(0), 0)/Π(q°) = (n − 1)/n` (and `Π(q°) > 0`). -/
theorem p53_lower_bound_ratio (M : Model) (n : ℕ) (hn : 2 ≤ n) (qo : ℝ)
    (hqo : M.F qo = (M.p - M.c) / M.p) :
    0 < M.chainProfit qo ∧
      M.supplierProfit (M.wb n 0 qo) 0 qo / M.chainProfit qo = ((n : ℝ) - 1) / n := by sorry

end CachonCoord.Proportional
