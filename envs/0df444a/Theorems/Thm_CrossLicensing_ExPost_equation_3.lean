-- Prove2me | Theorems.Thm_CrossLicensing_ExPost_equation_3
-- name    : CrossLicensing.ExPost.equation_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T11:27:24.172879+00:00
-- url     : https://prove2.me/theorems/86610c9d-ea20-4fdd-811a-cbd8e61466af
-- title:
--   Equation (3), p. 10 — supplier profit at the quantity equilibrium
-- statement:
--   Fix $0\le\beta\le1$, $0\le T_1\le T_2$, and $r\ge0$, and let $(q_1,q_2)$ be any Nash equilibrium of the quantity game (1). With $r_1=1+T_1(2-\beta)-T_2(1-2\beta)$ and $r_2=1+\beta T_1+T_2$, the supplier's profit is
--
--   $$
--   r(q_1+q_2)=\pi_s^{\mathrm{cl}}(r)=\begin{cases}
--   \dfrac{(2-2r+(T_1+T_2)(1+\beta))r}{3},&r\le r_1,\\
--   \dfrac{(1-r+\beta T_1+T_2)r}{2},&r_1<r\le r_2,\\
--   0,&r>r_2.
--   \end{cases}
--   $$
--
--   This connects the supplier's actual revenue at a strategic outcome to the paper's piecewise expression. At $\beta=0$ it gives equation (4), the no-licensing profit. **Formalization Note** The result applies to every Nash equilibrium; equilibrium existence is supplied by equation (2).
-- source:
--   Wang, Huang, Lee, Cross-licensing in a Supply Chain with Asymmetric Manufacturers, SSRN 3053682 (version of 2023-04-27), p. 10, equation (3), with equation (4) at beta = 0

import Mathlib
import Definitions.Def_CrossLicensing_ExPost_Model

namespace CrossLicensing.ExPost

/-- Equation (3), the supplier's profit at any quantity-game equilibrium. -/
theorem equation_3 (β T₁ T₂ r : ℝ) (h : Standing β T₁ T₂ r) (q : ℝ × ℝ)
    (hq : IsQuantityNE β T₁ T₂ r q) :
    supplierProfit r q = supplierProfitFormula β T₁ T₂ r := by sorry

end CrossLicensing.ExPost
