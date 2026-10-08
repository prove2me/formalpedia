-- Prove2me | Theorems.Thm_CachonCoord_Proportional_p52_supplier_deviation
-- name    : CachonCoord.Proportional.p52_supplier_deviation
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T04:44:39.143682+00:00
-- url     : https://prove2.me/theorems/52652d53-ccc0-4787-afef-70d42f6be55b
-- title:
--   p. 52 — ∂π_s(q°, ŵ(q°))/∂q = −q°pf(q°)/n < 0: the coordinating wholesale price is not optimal for the supplier
-- statement:
--   Let $n \ge 2$ and let $q^o$ solve (20). Under a wholesale-price contract the supplier who induces total stock $q$ earns $\pi_s(q, \widehat w(q)) = q(\widehat w(q) - c)$. This is differentiable in $q$ at $q^o$, with
--
--   $$
--   \frac{\partial \pi_s(q^o, \widehat w(q^o))}{\partial q} = -\frac{q^o p f(q^o)}{n},
--   $$
--
--   which is negative when the density satisfies $f(q^o) > 0$.
--
--   Hence the supplier prefers a higher wholesale price and a smaller quantity than $q^o$: the coordinating wholesale-price contract is not her optimal wholesale-price contract.
--
--   **Formalization Note** $f(q^o) > 0$ is an added hypothesis: a strictly increasing differentiable $F$ can have $f(q^o) = 0$, and then the derivative is $0$, not negative. The page does not state it. The hypotheses on the demand law are the chapter's standing assumptions (p. 7), carried by the model.
-- source:
--   Cachon (2003), Supply Chain Coordination with Contracts, 3rd draft (Jan. 2003), §6.5.1, p. 52 (π_s(q, ŵ(q)) and its derivative at q°)

import Mathlib
import Definitions.Def_CachonCoord_Proportional_Demand
import Definitions.Def_CachonCoord_Proportional_Nash
import Definitions.Def_CachonCoord_Proportional_Game

namespace CachonCoord.Proportional

/-- p. 52: with the wholesale price contract the supplier earns `π_s(q, ŵ(q)) = q (ŵ(q) − c)`;
"Assuming `n > 1`, differentiate `π_s(q, ŵ(q))` with respect to `q` and evaluate at `ŵ(q°)`, the
coordinating wholesale price, `∂π_s(q°, ŵ(q°))/∂q = −q° p f(q°)/n < 0`." The negativity needs
`f(q°) > 0`, assumed here. -/
theorem p52_supplier_deviation (M : Model) (n : ℕ) (hn : 2 ≤ n) (qo : ℝ)
    (hqo : M.F qo = (M.p - M.c) / M.p) (hf : 0 < M.density qo) :
    HasDerivAt (fun q => M.supplierProfit (M.what n q) 0 q)
        (-(qo * M.p * M.density qo) / n) qo ∧
      -(qo * M.p * M.density qo) / n < 0 := by sorry

end CachonCoord.Proportional
