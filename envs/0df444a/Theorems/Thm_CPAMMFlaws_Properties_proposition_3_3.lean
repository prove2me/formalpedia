-- Prove2me | Theorems.Thm_CPAMMFlaws_Properties_proposition_3_3
-- name    : CPAMMFlaws.Properties.proposition_3_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T21:27:27.505775+00:00
-- url     : https://prove2.me/theorems/53b5beb8-f838-4181-a8eb-fb719a21cd40
-- title:
--   Proposition 3(3), p. 22 — splitting a constant product pool into k equal pools and the order into k equal parts leaves the total cost unchanged
-- statement:
--   Let a constant product pool hold $X>0$ units of token $A$ and $Y>0$ units of token $B$, let $0<x<X$ and $k>0$. If the liquidity is split into $k$ equal pools $(X/k,\,Y/k)$ and the order into $k$ equal parts $x/k$, one on each pool, the total cost equals the cost on the single pool:
--
--   $$
--   p^{\mathrm{cmm}}(x,X,Y)=k\cdot p^{\mathrm{cmm}}\Bigl(\frac{x}{k},\frac{X}{k},\frac{Y}{k}\Bigr).
--   $$
--
--   Fragmenting liquidity across identical constant product pools, with the order split pro rata, does not change execution cost.
--
--   **Formalization Note** $X>0$, $Y>0$ are the deposits of §II.C, not printed in the proposition. $k$ is any positive real, as in the proposition's preamble "$k>0$".
-- source:
--   Park, The Conceptual Flaws of Constant Product Automated Market Making, working paper dated June 8, 2021, p. 22, Proposition 3(3)

import Mathlib
import Definitions.Def_CPAMMFlaws_Properties_Setting

namespace CPAMMFlaws.Properties

theorem proposition_3_3 (X Y x k : ℝ) (hX : 0 < X) (hY : 0 < Y)
    (hx : 0 < x) (hxX : x < X) (hk : 0 < k) :
    pcmm x X Y = k * pcmm (x / k) (X / k) (Y / k) := by sorry

end CPAMMFlaws.Properties
