-- Prove2me | Theorems.Thm_CPAMMFlaws_Properties_eq_4
-- name    : CPAMMFlaws.Properties.eq_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T21:27:38.934473+00:00
-- url     : https://prove2.me/theorems/e4373946-a378-47ec-8162-de0ea6911975
-- title:
--   (4), p. 23 — the front-runner's profit on a constant product pool is 2x²Y/((X − x)(X − 2x)) > 0
-- statement:
--   Let a constant product pool hold $X>0$ units of token $A$ and $Y>0$ units of token $B$, and let $0<x<X/2$. A front-runner buys $x$ units, the trader she front-runs buys $x$ units, and the pool is then $(X-2x,\;Y+y(2x))$ with $y(2x)=p^{\mathrm{cmm}}(2x,X,Y)$. She sells her $x$ units back into that pool. Then:
--
--   1. her sale proceeds are
--   $$
--   -p^{\mathrm{cmm}}\bigl(-x,\;X-2x,\;Y+y(2x)\bigr)=\frac{xXY}{(X-x)(X-2x)};
--   $$
--   2. her profit, the proceeds minus her purchase cost $p^{\mathrm{cmm}}(x,X,Y)$, is
--   $$
--   -p^{\mathrm{cmm}}\bigl(-x,\;X-2x,\;Y+y(2x)\bigr)-p^{\mathrm{cmm}}(x,X,Y)=\frac{2x^2Y}{(X-x)(X-2x)};
--   $$
--   3. this profit is strictly positive.
--
--   This is the computation behind Proposition 3(2): front-running a constant product pool is profitable for every order size.
--
--   **Formalization Note** The paper writes the proceeds as $y(-x,X-2x,Y+y(2x))$, the amount *received*; in the sign of (3) a sale has negative cost, so the proceeds are $-p^{\mathrm{cmm}}(-x,\cdot,\cdot)$ (p. 16: "Negative values of $x$ signify a sale and the cost, therefore, indicates revenue earned"). The bound $x<X/2$ is the paper's standing restriction for front-running (p. 19); $X>0$, $Y>0$ are the deposits of §II.C.
-- source:
--   Park, The Conceptual Flaws of Constant Product Automated Market Making, working paper dated June 8, 2021, p. 23, proof of Proposition 3(2), (4)

import Mathlib
import Definitions.Def_CPAMMFlaws_Properties_Setting

namespace CPAMMFlaws.Properties

theorem eq_4 (X Y x : ℝ) (hX : 0 < X) (hY : 0 < Y) (hx : 0 < x) (hx2 : x < X / 2) :
    -pcmm (-x) (X - 2 * x) (Y + pcmm (2 * x) X Y) = x * X * Y / ((X - x) * (X - 2 * x)) ∧
      -pcmm (-x) (X - 2 * x) (Y + pcmm (2 * x) X Y) - pcmm x X Y =
        2 * x ^ 2 * Y / ((X - x) * (X - 2 * x)) ∧
      0 < 2 * x ^ 2 * Y / ((X - x) * (X - 2 * x)) := by sorry

end CPAMMFlaws.Properties
