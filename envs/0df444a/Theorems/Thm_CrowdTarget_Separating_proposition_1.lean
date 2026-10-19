-- Prove2me | Theorems.Thm_CrowdTarget_Separating_proposition_1
-- name    : CrowdTarget.Separating.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T17:26:05.023932+00:00
-- url     : https://prove2.me/theorems/42a215cc-dd24-4f6a-8572-11a0ee4fa30e
-- title:
--   Proposition 1: under complete information the creator sets $C=S_i$, $p=v_i$
-- statement:
--   Under complete information all backers know the type $i\in\{H,L\}$, so at a price $p\le v_i$ every interested backer pledges and the expected profit is (1) with full demand,
--   $$
--   \Pi_i(C,p)=\int_{\{N\in[0,\bar N]\,:\,C\le pN\}}\frac{pN-S_i}{\bar N}\,dN .
--   $$
--   Among all designs satisfying the funding constraint $C\ge S_i$ and the pricing constraint $0<p\le v_i$, the design $(S_i,v_i)$ maximizes $\Pi_i$, and it is the only maximizer.
--
--   This is the complete-information benchmark against which the cost of signaling is measured.
-- source:
--   Chakraborty, Swinney, Signaling to the Crowd, SSRN 2885457 (rev. June 2019), p. 12, Proposition 1 (first sentence)

import Mathlib
import Definitions.Def_CrowdTarget_Separating_Setting

namespace CrowdTarget.Separating

/-- Chakraborty, Swinney, Signaling to the Crowd, SSRN 2885457 (rev. June 2019), p. 12, Proposition 1 (first sentence).

Under complete information every backer pledges at a price `p ≤ v_i`, so the expected profit (1)
of type `i` is `campaignProfit P 1 S_i C p`. Over the designs satisfying the funding constraint
`C ≥ S_i` and the pricing constraint `0 < p ≤ v_i` (p. 12), it is maximized at `(S_i, v_i)`, and
only there.

**Formalization Note** "sets target `C = S_i` … and price `p = v_i`" is read as: `(S_i, v_i)` is
the unique maximizer of (1) over the constrained designs. -/
theorem proposition_1 (P : Params) (hP : P.Standing) (i : CType) :
    (∀ d : Design, cost P i ≤ d.C → 0 < d.p → d.p ≤ val P i →
      campaignProfit P 1 (cost P i) d.C d.p ≤
        campaignProfit P 1 (cost P i) (cost P i) (val P i)) ∧
    (∀ d : Design, cost P i ≤ d.C → 0 < d.p → d.p ≤ val P i →
      campaignProfit P 1 (cost P i) d.C d.p =
        campaignProfit P 1 (cost P i) (cost P i) (val P i) →
      d = ⟨cost P i, val P i⟩) := by sorry

end CrowdTarget.Separating
