-- Prove2me | Theorems.Thm_BOGOPromo_NoStockpile_bogo_profit_eqs_1_2
-- name    : BOGOPromo.NoStockpile.bogo_profit_eqs_1_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T16:23:28.739219+00:00
-- url     : https://prove2.me/theorems/51567761-3b81-4541-822d-dfd0bf252206
-- title:
--   Eqs. (1)–(2), pp. 13–14 (PDF 13–14) — BOGO retailer profit in Cases I and II of Table 1
-- statement:
--   Fix $0<\theta\le 1$ and a wholesale price $w$. Consider a BOGO with first-unit price $p_b$ and second-unit price $p_g$, and let $\pi_{br}(p_b,p_g)$ and $D_b(p_b,p_g)$ be the retailer's expected profit and expected demand when every consumer with valuation $v\sim U[0,1]$ picks a utility-maximizing purchase option.
--
--   1. **Case I** ($\theta p_b\le p_g$). If $0\le p_b$ and $p_g\le\theta$, then
--   $$\pi_{br}(p_b,p_g)=2(1-p_b)(p_b-w)+\Bigl(1-\frac{p_g}{\theta}\Bigr)(p_g-w),\qquad D_b(p_b,p_g)=2(1-p_b)+\Bigl(1-\frac{p_g}{\theta}\Bigr).$$
--   2. **Case II** ($p_g<\theta p_b$). If $0\le p_g$ and $p_b\le 1$, then
--   $$\pi_{br}(p_b,p_g)=\Bigl(2-p_b-\frac{p_b+p_g}{1+\theta}\Bigr)(p_b-w)+\Bigl(1-\frac{p_b+p_g}{1+\theta}\Bigr)(p_g-w).$$
--
--   These identities connect the consumer-choice model to the closed-form profit functions that the retailer optimizes in Proposition 1.
--
--   **Formalization Note** The side conditions $p_g\le\theta$ (Case I) and $p_b\le 1$ (Case II) keep the consumer segments of Table 1 inside $[0,1]$; the paper uses them silently. The demand identity of Case I is the expected number of units, used for the manufacturer's profit (3).
-- source:
--   Li, Khouja, Pan & Zhou, Buy-One-Get-One Promotions in a Two-Echelon Supply Chain, SSRN working paper 3561162, pp. 13–14 (PDF 13–14), eqs. (1), (2) and Table 1

import Mathlib
import Definitions.Def_BOGOPromo_NoStockpile_Model

namespace BOGOPromo.NoStockpile

theorem bogo_profit_eqs_1_2 (θ w pb pg : ℝ) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) :
    (0 ≤ pb → θ * pb ≤ pg → pg ≤ θ →
      bogoProfit θ w pb pg = 2 * (1 - pb) * (pb - w) + (1 - pg / θ) * (pg - w) ∧
      bogoDemand θ pb pg = 2 * (1 - pb) + (1 - pg / θ)) ∧
    (0 ≤ pg → pg < θ * pb → pb ≤ 1 →
      bogoProfit θ w pb pg =
        (2 - pb - (pb + pg) / (1 + θ)) * (pb - w) + (1 - (pb + pg) / (1 + θ)) * (pg - w)) := by sorry

end BOGOPromo.NoStockpile
