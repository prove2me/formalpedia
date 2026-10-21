-- Prove2me | Theorems.Thm_BOGOPromo_NoStockpile_pr_profit_eq_4
-- name    : BOGOPromo.NoStockpile.pr_profit_eq_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T16:23:30.10583+00:00
-- url     : https://prove2.me/theorems/2fb25cf7-a4b3-4193-99d4-3eb91a0d5331
-- title:
--   Eq. (4), p. 19 (PDF 19) — PR retailer profit, identical in Cases I and II of Table 4
-- statement:
--   Fix $0<\theta\le 1$ and a wholesale price $w$. Consider a price reduction with discount price $p_d$ in period 1 and regular price $p_r$ in period 2, and let $\pi_{dr}(p_r,p_d)$ and $D_d(p_r,p_d)$ be the retailer's expected profit and expected demand when every consumer with valuation $v\sim U[0,1]$ picks a utility-maximizing purchase option. If $0\le p_d\le p_r\le 1$ and $p_d\le\theta$, then
--   $$\pi_{dr}(p_r,p_d)=(1-p_r)(p_r-w)+\Bigl(2-p_d-\frac{p_d}{\theta}\Bigr)(p_d-w),\qquad D_d(p_r,p_d)=(1-p_r)+\Bigl(2-p_d-\frac{p_d}{\theta}\Bigr).$$
--
--   The same formula covers both consumer segmentations of Table 4 ($p_d/\theta\ge p_r$ and $p_d/\theta<p_r$), and is the objective of the retailer's problem in Proposition 3.
--
--   **Formalization Note** The conditions $p_r\le 1$ and $p_d\le\theta$ keep the segments of Table 4 inside $[0,1]$; the paper uses them silently. The demand identity is the expected number of units, used in the manufacturer's profit (5).
-- source:
--   Li, Khouja, Pan & Zhou, Buy-One-Get-One Promotions in a Two-Echelon Supply Chain, SSRN working paper 3561162, p. 19 (PDF 19), eq. (4) and Table 4 (p. 20)

import Mathlib
import Definitions.Def_BOGOPromo_NoStockpile_Model

namespace BOGOPromo.NoStockpile

theorem pr_profit_eq_4 (θ w pr pd : ℝ) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1)
    (hpd0 : 0 ≤ pd) (hpdr : pd ≤ pr) (hpr1 : pr ≤ 1) (hpdθ : pd ≤ θ) :
    prProfit θ w pr pd = (1 - pr) * (pr - w) + (2 - pd - pd / θ) * (pd - w) ∧
    prDemand θ pr pd = (1 - pr) + (2 - pd - pd / θ) := by sorry

end BOGOPromo.NoStockpile
