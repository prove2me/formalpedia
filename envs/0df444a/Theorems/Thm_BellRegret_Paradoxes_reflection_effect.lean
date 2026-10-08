-- Prove2me | Theorems.Thm_BellRegret_Paradoxes_reflection_effect
-- name    : BellRegret.Paradoxes.reflection_effect
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T01:22:30.646661+00:00
-- url     : https://prove2.me/theorems/df4f87ce-4cfc-44d9-83ca-1afa79969fdf
-- title:
--   Sec. 2(ii), p. 973 — the reflection effect is a consequence of u(x, y) = x + f(x − y)
-- statement:
--   Let $f:\mathbb R\to\mathbb R$, let $u(x,y)=x+f(x-y)$, and let $p,x_1,x_2,x_3\in\mathbb R$. Compare a sure amount with a lottery giving one amount with probability $p$ and another with probability $1-p$. Then the decision maker is indifferent between $x_2$ for sure and the lottery $(p:\,x_1;\ 1-p:\,x_3)$, i.e.
--   $$p[x_2+f(x_2-x_1)]+(1-p)[x_2+f(x_2-x_3)]=p[x_1+f(x_1-x_2)]+(1-p)[x_3+f(x_3-x_2)],$$
--   if and only if she is indifferent between $-x_2$ for sure and the lottery $(p:\,-x_1;\ 1-p:\,-x_3)$, i.e.
--   $$p[-x_2+f(-x_2+x_1)]+(1-p)[-x_2+f(-x_2+x_3)]=p[-x_1+f(-x_1+x_2)]+(1-p)[-x_3+f(-x_3+x_2)].$$
--
--   This is the reflection effect of Kahneman and Tversky: indifference for gains carries over to the mirrored losses, with no special role for the current asset position.
--
--   **Formalization Note** On p. 973 the last bracket of the second equality is printed $[x_3+f(-x_3+x_2)]$; with $u(-x_3,-x_2)=-x_3+f(-x_3+x_2)$ it must be $[-x_3+f(-x_3+x_2)]$, and as printed the two equalities differ by $2(1-p)x_3$. The formalization states the indifference of the mirrored alternatives, i.e. the corrected display. It holds for every real $p$.
-- source:
--   Bell, Regret in Decision Making under Uncertainty, Operations Research 30(5) (1982) 961–981, p. 973 (PDF 14), Sec. 2(ii), the two displayed indifferences and "These two equalities are identical"

import Mathlib
import Definitions.Def_BellRegret_Paradoxes_Model

namespace BellRegret.Paradoxes

/-- Sec. 2(ii), p. 973 (the reflection effect): `x₂` for sure is indifferent to a `p`-chance
at `x₁` and a `(1 − p)`-chance at `x₃` if and only if `−x₂` for sure is indifferent to a
`p`-chance at `−x₁` and a `(1 − p)`-chance at `−x₃`. -/
theorem reflection_effect (f : ℝ → ℝ) (p x₁ x₂ x₃ : ℝ) :
    Indiff f (prob2 p) ![x₂, x₂] ![x₁, x₃] ↔
      Indiff f (prob2 p) ![-x₂, -x₂] ![-x₁, -x₃] := by sorry

end BellRegret.Paradoxes
