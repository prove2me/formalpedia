-- Prove2me | Theorems.Thm_CrossLicensing_ExPost_equation_2
-- name    : CrossLicensing.ExPost.equation_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T11:27:17.041918+00:00
-- url     : https://prove2.me/theorems/b97aef3c-a979-499f-bbce-ce2e2ff2539d
-- title:
--   Equation (2), p. 10 — the downstream Cournot equilibrium
-- statement:
--   Fix $0\le\beta\le1$, $0\le T_1\le T_2$, and $r\ge0$. Let $r_1=1+T_1(2-\beta)-T_2(1-2\beta)$ and $r_2=1+\beta T_1+T_2$. A quantity profile is a Nash equilibrium of the manufacturers' nonnegative-quantity game (1) exactly when it equals
--
--   $$
--   (q_1,q_2)=\begin{cases}
--   \left(\dfrac{1-r+T_1(2-\beta)+T_2(-1+2\beta)}{3},\dfrac{1-r+T_1(-1+2\beta)+T_2(2-\beta)}{3}\right),&r\le r_1,\\
--   \left(0,\dfrac{1-r+\beta T_1+T_2}{2}\right),&r_1<r\le r_2,\\
--   (0,0),&r>r_2.
--   \end{cases}
--   $$
--
--   Thus the displayed outcome exists and is the unique quantity equilibrium, including both regime boundaries. **Formalization Note** The paper's first line of (2) has an unclosed parenthesis; the intended first quantity is the fraction shown above. The nonnegative wholesale-price domain is explicit.
-- source:
--   Wang, Huang, Lee, Cross-licensing in a Supply Chain with Asymmetric Manufacturers, SSRN 3053682 (version of 2023-04-27), p. 10, equation (2)

import Mathlib
import Definitions.Def_CrossLicensing_ExPost_Model

namespace CrossLicensing.ExPost

/-- Equation (2), read as an exact characterization of the quantity-game equilibrium. -/
theorem equation_2 (β T₁ T₂ r : ℝ) (h : Standing β T₁ T₂ r) (q : ℝ × ℝ) :
    IsQuantityNE β T₁ T₂ r q ↔ q = quantityFormula β T₁ T₂ r := by sorry

end CrossLicensing.ExPost
