-- Prove2me | Theorems.Thm_CrossLicensing_ExAnte_supplier_profit_closed
-- name    : CrossLicensing.ExAnte.supplier_profit_closed
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T14:39:41.247007+00:00
-- url     : https://prove2.me/theorems/55c61705-fb75-4573-a999-1d10c60f5e59
-- title:
--   Proof of Proposition 2, p. A.1 — the supplier's attained equilibrium profit in both regimes
-- statement:
--   Fix $0\le\beta\le1$ and $49/144<k_2<k_1$. At the appendix's named innovation outcome $T^*(\beta)$, the supplier chooses a nonnegative wholesale price. Its maximum is attained and equals the printed boundary or interior expression according to the investment-cost threshold:
--
--   $$\max_{r\ge0}\pi_s(\beta,T^*(\beta),r)=\begin{cases}\pi_s^B(\beta),&k_2<\hat k_2(k_1\mid\beta),\\\pi_s^I(\beta),&k_2\ge\hat k_2(k_1\mid\beta).\end{cases}$$
--
--   Here $\pi_s^B$ and $\pi_s^I$ are the explicit rational formulas displayed on page A.1. This identifies the supplier's actual price-optimization value with the expressions used in the later preference comparison.
--
--   **Formalization Note** The statement uses `IsGreatest` on the set of revenue values at all $r\ge0$, which asserts both attainment and optimality. Its quantity formula is display (2), in the paper's $T_2\ge T_1$ ordering.
-- source:
--   Wang, Huang, Lee, Cross-licensing in a Supply Chain with Asymmetric Manufacturers, SSRN 3053682 (version of 2023-04-27), p. A.1 (PDF 33), proof of Proposition 2, formulas for π^I_s and π^B_s

import Definitions.Def_CrossLicensing_ExAnte_Model

namespace CrossLicensing.ExAnte

/-- Proof of Proposition 2, p. A.1: the printed formulas are the attained
supplier optimum at the paper's equilibrium innovation levels. -/
theorem supplier_profit_closed (β k1 k2 : ℝ) (h : CrossLicensing.Innovation.Standing β k1 k2) :
    IsGreatest
      ((fun r : ℝ => supplierProfit β (equilibriumT1 β k1 k2)
        (equilibriumT2 β k1 k2) r) '' Set.Ici (0 : ℝ))
      (if k2 < khat2 k1 β then piBoundary β k1 else piInterior β k1 k2) := by sorry

end CrossLicensing.ExAnte
