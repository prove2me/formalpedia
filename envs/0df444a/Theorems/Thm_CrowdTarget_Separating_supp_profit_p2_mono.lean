-- Prove2me | Theorems.Thm_CrowdTarget_Separating_supp_profit_p2_mono
-- name    : CrowdTarget.Separating.supp_profit_p2_mono
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T17:26:07.540621+00:00
-- url     : https://prove2.me/theorems/6f26c464-0203-4f2b-906f-7d5a23e702ce
-- title:
--   The H-type profit along $p=p_2(C)$ increases on $[S_H,C^*]$
-- statement:
--   Let $\alpha^*<\alpha\le1$, and let $\Pi_H(C,p)$ be the H-type's expected profit when believed to be of type $H$. The map
--   $$
--   C\longmapsto\Pi_H\bigl(C,p_2(C)\bigr)
--   $$
--   is nondecreasing on $[S_H,C^*(\alpha)]$, and strictly increasing there unless $\alpha=1$ and $S_L=S_H$.
--
--   In the paper this is the sign of the derivative $d\Pi_H(C,p_2(C))/dC\ge0$, with equality only when $\alpha=1$ and $S_L=S_H$; it singles out the right end of the curve, $(C^*,v_H)$, as the H-type's best mimicking-proof design.
--
--   **Formalization Note** The derivative bound is replaced by the monotonicity it is used for.
-- source:
--   Chakraborty, Swinney, Signaling to the Crowd, SSRN 2885457 (rev. June 2019), Online Supplement p. 5, proof of Proposition 3 (derivative display)

import Mathlib
import Definitions.Def_CrowdTarget_Separating_Setting

namespace CrowdTarget.Separating

/-- Chakraborty, Swinney, Signaling to the Crowd, SSRN 2885457 (rev. June 2019), Online Supplement p. 5, the derivative display.

For `α∗ < α ≤ 1`, the H-type's profit along the curve `p = p₂(C)`, `C ↦ Π_H(C, p₂(C))`, is
nondecreasing on `[S_H, C∗(α)]`, and strictly increasing there unless `α = 1` and `S_L = S_H`.

**Formalization Note** The printed derivative inequality is replaced by the monotonicity it is
used for; `Π_H` is the H-type's profit when believed to be H. -/
theorem supp_profit_p2_mono (P : Params) (hP : P.Standing) (α : ℝ) (hα : alphaStar P < α)
    (hα1 : α ≤ 1) :
    MonotoneOn (fun C => profit P α .H .H ⟨C, p2 P α C⟩) (Set.Icc P.SH (Cstar P α)) ∧
    (¬ (α = 1 ∧ P.SL = P.SH) →
      StrictMonoOn (fun C => profit P α .H .H ⟨C, p2 P α C⟩) (Set.Icc P.SH (Cstar P α))) := by sorry

end CrowdTarget.Separating
