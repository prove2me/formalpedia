-- Prove2me | Theorems.Thm_CrowdTarget_Separating_supp_informed_deviation
-- name    : CrowdTarget.Separating.supp_informed_deviation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T17:26:04.309967+00:00
-- url     : https://prove2.me/theorems/1d0dff3b-4be1-42af-8023-ce09cf58b818
-- title:
--   Selling only to informed backers does not pay: $\Pi_H(C^*,v_H)>\Pi_H(S_H,v_H)$
-- statement:
--   Let $\alpha^*<\alpha\le1$. If the H-type abandons signaling and offers $(S_H,v_H)$, she is believed to be of type $L$ and only the informed share $1-\alpha$ of the backers pledges, so her profit is Online Supplement (4),
--   $$
--   \Pi_H(S_H,v_H)=\frac{\bar N}{2}(1-\alpha)v_H+\frac{S_H^2}{2\bar N(1-\alpha)v_H}-S_H\ \text{ if }\ \frac{S_H}{(1-\alpha)v_H}<\bar N,\ \text{ and }0\text{ otherwise.}
--   $$
--   This is strictly less than her equilibrium profit $\Pi_H(C^*,v_H)$, where all backers pledge.
-- source:
--   Chakraborty, Swinney, Signaling to the Crowd, SSRN 2885457 (rev. June 2019), Online Supplement p. 5, proof of Proposition 3 (last paragraph; deviation profit Online Supplement (4), p. 3)

import Mathlib
import Definitions.Def_CrowdTarget_Separating_Setting

namespace CrowdTarget.Separating

/-- Chakraborty, Swinney, Signaling to the Crowd, SSRN 2885457 (rev. June 2019), Online Supplement p. 5, last paragraph of the proof of Proposition 3.

For `α∗ < α ≤ 1`, the H-type's equilibrium profit `Π_H(C∗, v_H)` strictly exceeds the profit of
the deviation to `(S_H, v_H)` believed L, which sells to the informed backers only
(Online Supplement (4), p. 3).

**Formalization Note** The deviation profit is `profit P α .H .L ⟨S_H, v_H⟩`, whose demand share
is `1 − α`; at `α = 1` it is `0`. -/
theorem supp_informed_deviation (P : Params) (hP : P.Standing) (α : ℝ) (hα : alphaStar P < α)
    (hα1 : α ≤ 1) :
    profit P α .H .L ⟨P.SH, P.vH⟩ < profit P α .H .H ⟨Cstar P α, P.vH⟩ := by sorry

end CrowdTarget.Separating
