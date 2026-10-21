-- Prove2me | Theorems.Thm_EcoOffset_Subgame_segOpt_spec
-- name    : EcoOffset.Subgame.segOpt_spec
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:26:59.548858+00:00
-- url     : https://prove2.me/theorems/0460a728-d94f-4f17-b51c-354368143875
-- title:
--   Online Supplement p. 1 (PDF 34) — the segment-optimal emission e_{x,a} exists, is unique, solves the first-order condition, and e_{0,a} = ē
-- statement:
--   Assume the standing assumptions of the model. Fix a segment size $a\in[0,1]$ and $x\ge0$. Then the problem
--   $$\max_{e\in[0,\bar e]}\; -(c(e)+xe)\,a\,m-f(e)$$
--   has exactly one maximizer, the segment-optimal emission $e_{x,a}$. Moreover:
--   1. every $e\in[0,\bar e]$ satisfying the first-order condition $[x+c'(e)]\,a\,m+f'(e)=0$ equals $e_{x,a}$;
--   2. $e_{0,a}=\bar e$.
--
--   The paper defines $e_{x,a}=\max(\min(\tilde e_{x,a},\bar e),0)$ with $\tilde e_{x,a}$ the root of the first-order condition. This statement makes that definition well posed and pins down the interior case; it is the basic tool for every profile value in the mission.
--
--   **Formalization Note** The root $\tilde e_{x,a}$ need not exist (at $x=0$ the first-order condition has no root, since $c',f'<0$), and outside $[0,\bar e]$ it depends on $c,f$ where the paper assumes nothing. The mission therefore defines $e_{x,a}$ as the maximizer; item 1 recovers the paper's description whenever the root lies in $[0,\bar e]$.
-- source:
--   Gao & Souza, Carbon Offsetting with Eco-Conscious Consumers, SSRN 3440652 (copy held, sha256 e7d7f85a…7306), Online Supplement p. 1 (PDF 34), definition of e_{x,α}

import Mathlib
import Definitions.Def_EcoOffset_Subgame_Model

namespace EcoOffset.Subgame

/-- Online Supplement p. 1: for `a ∈ [0, 1]` and `x ≥ 0`, the segment-optimal emission
`e_{x,a}` maximizes `−(c(e) + x e) a m − f(e)` over `[0, ¯e]`, the maximizer is unique, every
point of `[0, ¯e]` satisfying the first-order condition `[x + c′(e)] a m + f′(e) = 0` is it, and
`e_{0,a} = ¯e`. -/
theorem segOpt_spec (P : Params) (hS : P.Standing) (x a : ℝ) (hx : 0 ≤ x)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    IsSegOpt P x a (segOpt P x a) ∧
    (∀ e, IsSegOpt P x a e → e = segOpt P x a) ∧
    (∀ e ∈ Set.Icc 0 P.ebar,
      (x + deriv P.c e) * a * P.m + deriv P.f e = 0 → segOpt P x a = e) ∧
    segOpt P 0 a = P.ebar := by sorry

end EcoOffset.Subgame
