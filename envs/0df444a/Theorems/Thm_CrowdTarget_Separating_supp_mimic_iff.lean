-- Prove2me | Theorems.Thm_CrowdTarget_Separating_supp_mimic_iff
-- name    : CrowdTarget.Separating.supp_mimic_iff
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T17:26:18.756217+00:00
-- url     : https://prove2.me/theorems/be186183-55a1-4b2b-af19-32158741db29
-- title:
--   The L-type does not mimic $(C,p)$ iff $p_1(C)\le p\le p_2(C)$
-- statement:
--   Let $0<\alpha\le1$, $C\ge S_H$, $v_L<p\le v_H$ and $C<\alpha p\bar N$. An L-type who copies the design $(C,p)$ and is believed to be of type $H$ is backed by the uninformed backers only, and earns
--   $$
--   \Pi_L(C,p)=\frac{\bar N}{2}\alpha p+\frac{2S_LC-C^2}{2\bar N\alpha p}-S_L .
--   $$
--   Then $\Pi_L(C,p)\le\Pi_L(S_L,v_L)$ if and only if
--   $$
--   p_1(C)\le p\le p_2(C),\qquad p_{1,2}(C)=\frac{B\mp\sqrt{B^2+4\frac{C^2-2S_LC}{\bar N^2}}}{2\alpha}.
--   $$
--
--   This turns the L-type's incentive constraint into an explicit price window for the H-type's signal.
-- source:
--   Chakraborty, Swinney, Signaling to the Crowd, SSRN 2885457 (rev. June 2019), Online Supplement p. 4, (5)–(7)

import Mathlib
import Definitions.Def_CrowdTarget_Separating_Setting

namespace CrowdTarget.Separating

/-- Chakraborty, Swinney, Signaling to the Crowd, SSRN 2885457 (rev. June 2019), Online Supplement p. 4, (5)–(7): the no-mimic condition.

For `0 < α ≤ 1`, a target `C ≥ S_H` and a price `v_L < p ≤ v_H` with `C < α p N̄`, an L-type who
copies the design `(C, p)` and is believed to be H sells to the uninformed backers only, and she
earns no more than at `(S_L, v_L)` if and only if `p₁(C) ≤ p ≤ p₂(C)`.

**Formalization Note** The mimicking profit is `profit P α .L .H ⟨C, p⟩`, whose demand share is
`α` because `v_L < p ≤ v_H` (§3.1 pledging rules). -/
theorem supp_mimic_iff (P : Params) (hP : P.Standing) (α C p : ℝ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hC : P.SH ≤ C) (hpL : P.vL < p) (hpH : p ≤ P.vH) (hsucc : C < α * p * P.Nbar) :
    profit P α .L .H ⟨C, p⟩ ≤ profit P α .L .L ⟨P.SL, P.vL⟩ ↔
      p1 P α C ≤ p ∧ p ≤ p2 P α C := by sorry

end CrowdTarget.Separating
