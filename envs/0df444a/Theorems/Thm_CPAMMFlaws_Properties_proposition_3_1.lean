-- Prove2me | Theorems.Thm_CPAMMFlaws_Properties_proposition_3_1
-- name    : CPAMMFlaws.Properties.proposition_3_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T21:27:22.953761+00:00
-- url     : https://prove2.me/theorems/4d8a3503-0590-4258-8b0f-0a7c418885f9
-- title:
--   Proposition 3(1), p. 22 — additivity: buying αx and then (1 − α)x from a constant product pool costs the same as buying x at once
-- statement:
--   Let a constant product pool hold $X>0$ units of token $A$ and $Y>0$ units of token $B$, let $0<x<X$ and $0<\alpha<1$. Buying $\alpha x$ units first, and then $(1-\alpha)x$ units from the pool left by the first trade, $(X-\alpha x,\;Y+y(\alpha x,X,Y))$, costs exactly as much as buying $x$ units in one trade:
--
--   $$
--   p^{\mathrm{cmm}}(\alpha x,X,Y)+p^{\mathrm{cmm}}\bigl((1-\alpha)x,\;X-\alpha x,\;Y+y(\alpha x,X,Y)\bigr)=p^{\mathrm{cmm}}(x,X,Y),
--   $$
--
--   where $y(\alpha x,X,Y)=p^{\mathrm{cmm}}(\alpha x,X,Y)$.
--
--   So splitting an order in time does not change its total cost on a constant product pool.
--
--   **Formalization Note** $X>0$, $Y>0$ are the deposits of §II.C, not printed in the proposition. The pool after the first trade is written in the printed form $Y+p^{\mathrm{cmm}}(\alpha x,X,Y)$.
-- source:
--   Park, The Conceptual Flaws of Constant Product Automated Market Making, working paper dated June 8, 2021, p. 22, Proposition 3(1)

import Mathlib
import Definitions.Def_CPAMMFlaws_Properties_Setting

namespace CPAMMFlaws.Properties

theorem proposition_3_1 (X Y x α : ℝ) (hX : 0 < X) (hY : 0 < Y)
    (hx : 0 < x) (hxX : x < X) (hα : 0 < α) (hα1 : α < 1) :
    pcmm (α * x) X Y + pcmm ((1 - α) * x) (X - α * x) (Y + pcmm (α * x) X Y) =
      pcmm x X Y := by sorry

end CPAMMFlaws.Properties
