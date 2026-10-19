-- Prove2me | Theorems.Thm_CrowdTarget_Separating_proposition_1_separating
-- name    : CrowdTarget.Separating.proposition_1_separating
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T17:26:12.525983+00:00
-- url     : https://prove2.me/theorems/7bcf4929-db8d-45d6-ab35-9a99693f92d0
-- title:
--   Proposition 1: the L-type plays $(S_L,v_L)$ in every separating equilibrium
-- statement:
--   Fix an uninformed fraction $\alpha\in[0,1]$. In every separating equilibrium $(d_L,d_H)$ of the target-and-price signaling game (uninformed backers believe $H$ exactly at $d_H$ and $L$ elsewhere), the L-type's design is her complete-information design:
--   $$
--   d_L=(S_L,v_L).
--   $$
--
--   The L-type gains nothing from being identified, so she does as well as she can on her own; this pins down one half of every separating equilibrium.
-- source:
--   Chakraborty, Swinney, Signaling to the Crowd, SSRN 2885457 (rev. June 2019), p. 12, Proposition 1 (second sentence)

import Mathlib
import Definitions.Def_CrowdTarget_Separating_Setting

namespace CrowdTarget.Separating

/-- Chakraborty, Swinney, Signaling to the Crowd, SSRN 2885457 (rev. June 2019), p. 12, Proposition 1 (second sentence).

In the presence of information asymmetry, the L-type sets target `C = S_L` and price `p = v_L` in
any separating equilibrium, for every uninformed fraction `α ∈ [0, 1]`.

**Formalization Note** The separating equilibrium is `IsSepEq` (p. 11, off-path belief L); no
refinement is needed for this part. -/
theorem proposition_1_separating (P : Params) (hP : P.Standing) (α : ℝ) (hα0 : 0 ≤ α)
    (hα1 : α ≤ 1) (dL dH : Design) (h : IsSepEq P α dL dH) :
    dL = ⟨P.SL, P.vL⟩ := by sorry

end CrowdTarget.Separating
