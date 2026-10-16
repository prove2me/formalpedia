-- Prove2me | Theorems.Thm_CPAMMFlaws_Properties_proposition_3
-- name    : CPAMMFlaws.Properties.proposition_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T21:27:22.394032+00:00
-- url     : https://prove2.me/theorems/566c1c2c-55d4-4739-b6e6-bdee32223c4b
-- title:
--   Proposition 3, pp. 22–23 — constant product pricing is additive and split-liquidity invariant, yet front-running (x < X/2) and two-venue arbitrage are strictly profitable
-- statement:
--   Let a constant product pool hold $X>0$ units of token $A$ and $Y>0$ units of token $B$, with cost function $p^{\mathrm{cmm}}(x,X,Y)=xY/(X-x)$ and $y(\cdot)=p^{\mathrm{cmm}}(\cdot,X,Y)$. Selling $q>0$ units of $A$ into a pool $(X',Y')$ earns $-p^{\mathrm{cmm}}(-q,X',Y')$. For $x\in(0,X)$, $\alpha\in(0,1)$ and $k>0$:
--
--   1. **Additivity:**
--   $$
--   p^{\mathrm{cmm}}(\alpha x,X,Y)+p^{\mathrm{cmm}}\bigl((1-\alpha)x,\;X-\alpha x,\;Y+y(\alpha x)\bigr)=p^{\mathrm{cmm}}(x,X,Y).
--   $$
--   2. **Profitable front-running:** if moreover $x<X/2$, buying $x$ ahead of another buy of $x$ and then selling $x$ into the pool $(X-2x,\,Y+y(2x))$ is strictly profitable,
--   $$
--   -p^{\mathrm{cmm}}(x,X,Y)-p^{\mathrm{cmm}}\bigl(-x,\;X-2x,\;Y+y(2x)\bigr)>0.
--   $$
--   3. **Additivity with split liquidity:**
--   $$
--   p^{\mathrm{cmm}}(x,X,Y)=k\cdot p^{\mathrm{cmm}}(x/k,\,X/k,\,Y/k).
--   $$
--   4. **Multi-venue arbitrage:** with two identical pools $(X,Y)$, after a buy of $x$ on the first one, selling $\alpha x$ into the first pool, now $(X-x,\,Y+y(x))$, and buying $\alpha x$ on the second is strictly profitable,
--   $$
--   -p^{\mathrm{cmm}}\bigl(-\alpha x,\;X-x,\;Y+y(x)\bigr)-p^{\mathrm{cmm}}(\alpha x,X,Y)>0 .
--   $$
--
--   The proposition shows that constant product pricing has the two consistency properties one expects of a market maker (1 and 3), yet exposes every order to profitable front-running and every trade to profitable arbitrage against an identical second venue.
--
--   **Formalization Note** Parts 2 and 4 are printed with $+p^{\mathrm{cmm}}(-x,\dots)$ and $p^{\mathrm{cmm}}(-\alpha x,\dots)$ as if these were the proceeds of the sale; the proofs (p. 23–24) use the amount received, which in the sign of (3) is $-p^{\mathrm{cmm}}(-q,\dots)$. Read literally, the printed left-hand sides are negative, so the statement poses the proceeds reading. Part 4 prints the first pool as $(X-x,\,Y-y(x))$; after a buy of $x$ that pool holds $Y+y(x)=XY/(X-x)$ (p. 15), and the statement uses $Y+y(x)$. Part 2 carries $x<X/2$, the paper's restriction for front-running (p. 19). $X>0$, $Y>0$ are the deposits of §II.C.
-- source:
--   Park, The Conceptual Flaws of Constant Product Automated Market Making, working paper dated June 8, 2021, pp. 22–23, Proposition 3

import Mathlib
import Definitions.Def_CPAMMFlaws_Properties_Setting

namespace CPAMMFlaws.Properties

theorem proposition_3 (X Y x α k : ℝ) (hX : 0 < X) (hY : 0 < Y)
    (hx : 0 < x) (hxX : x < X) (hα : 0 < α) (hα1 : α < 1) (hk : 0 < k) :
    pcmm (α * x) X Y + pcmm ((1 - α) * x) (X - α * x) (Y + pcmm (α * x) X Y) = pcmm x X Y ∧
      (x < X / 2 → 0 < -pcmm x X Y - pcmm (-x) (X - 2 * x) (Y + pcmm (2 * x) X Y)) ∧
      pcmm x X Y = k * pcmm (x / k) (X / k) (Y / k) ∧
      0 < -pcmm (-(α * x)) (X - x) (Y + pcmm x X Y) - pcmm (α * x) X Y := by sorry

end CPAMMFlaws.Properties
