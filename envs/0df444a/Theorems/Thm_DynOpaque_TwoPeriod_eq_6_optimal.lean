-- Prove2me | Theorems.Thm_DynOpaque_TwoPeriod_eq_6_optimal
-- name    : DynOpaque.TwoPeriod.eq_6_optimal
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:22:23.496685+00:00
-- url     : https://prove2.me/theorems/740117d7-2659-4cfb-bf24-4a24d3d1ae3a
-- title:
--   Claim after eq. (6), p. 13 — at p1 = p2 = vL the optimal decisions are ξ1 = ξ2 = 0, earning 2(vL − cL)
-- statement:
--   Assume $v_H>v_L$, $c_H>c_L$, $0\le\alpha\le1$, $c_L\le v_L$, and consider objective (6), the profit at $p_1=p_2=v_L$,
--   $$
--   \Pi(\xi_1,\xi_2\mid v_L,v_L)=[v_L-\xi_1c_H-(1-\xi_1)c_L]+[v_L-\xi_2c_H-(1-\xi_2)c_L].
--   $$
--   Then $(\xi_1,\xi_2)=(0,0)$ maximizes (6) over $[0,1]^2$, and its value is $2(v_L-c_L)$.
--
--   At the low price everyone buys in both periods, so delivering the expensive version is pure cost: the firm sells $L$ transparently.
-- source:
--   Huang and Yin, Dynamic Probabilistic Selling When Customers Have Boundedly Rational Expectations, SSRN manuscript 3627927, p. 13, claim after eq. (6)

import Mathlib
import Definitions.Def_DynOpaque_TwoPeriod_Model

namespace DynOpaque.TwoPeriod

/-- Claim after display (6), p. 13: with `p₁ = p₂ = vL` the optimal offering decisions are
`ξ₁ = ξ₂ = 0`, i.e. transparent selling of product `L`, earning `2(vL − cL)`. -/
theorem eq_6_optimal (vH vL cH cL α : ℝ) (hS : Standing vH vL cH cL α) :
    IsOptimalOffering (obj6 vL cH cL) 0 0 ∧ obj6 vL cH cL 0 0 = 2 * (vL - cL) := by sorry

end DynOpaque.TwoPeriod
