-- Prove2me | Theorems.Thm_DynOpaque_TwoPeriod_lemma_3
-- name    : DynOpaque.TwoPeriod.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:22:22.74955+00:00
-- url     : https://prove2.me/theorems/411de37d-3774-40db-af90-602e71e541b1
-- title:
--   Lemma 3, p. 12 — optimal offering probabilities at p1 = vHL, p2 = vL
-- statement:
--   Assume $v_H>v_L$, $c_H>c_L$, $0\le\alpha\le1$, $c_L\le v_L$, let $v_{HL}=\frac{v_H-v_L}{2}+v_L$, and consider objective (4), the profit at $p_1=v_{HL}$, $p_2=v_L$, over $(\xi_1,\xi_2)\in[0,1]^2$. Then:
--
--   1. if $\frac{v_{HL}-c_L}{c_H-c_L}<2$, an optimal decision is
--   $$
--   \xi_1=\frac{v_{HL}-c_L}{2(c_H-c_L)},\qquad \xi_2=0;
--   $$
--   2. if $\frac{v_{HL}-c_L}{c_H-c_L}\ge2$, an optimal decision is $\xi_1=1$, $\xi_2=0$.
--
--   "Optimal" means that the stated pair lies in $[0,1]^2$ and maximizes (4) over $[0,1]^2$; uniqueness is not claimed. At the low second-period price every period-2 customer buys, so the firm delivers the cheaper version then.
-- source:
--   Huang and Yin, Dynamic Probabilistic Selling When Customers Have Boundedly Rational Expectations, SSRN manuscript 3627927, p. 12, Lemma 3

import Mathlib
import Definitions.Def_DynOpaque_TwoPeriod_Model

namespace DynOpaque.TwoPeriod

/-- Lemma 3, p. 12: optimal offering decisions for objective (4) (`p₁ = vHL`, `p₂ = vL`). -/
theorem lemma_3 (vH vL cH cL α : ℝ) (hS : Standing vH vL cH cL α) :
    ((vHL vH vL - cL) / (cH - cL) < 2 →
      IsOptimalOffering (obj4 vH vL cH cL) ((vHL vH vL - cL) / (2 * (cH - cL))) 0) ∧
    ((vHL vH vL - cL) / (cH - cL) ≥ 2 →
      IsOptimalOffering (obj4 vH vL cH cL) 1 0) := by sorry

end DynOpaque.TwoPeriod
