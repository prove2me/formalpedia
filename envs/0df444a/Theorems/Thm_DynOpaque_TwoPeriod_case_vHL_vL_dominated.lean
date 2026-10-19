-- Prove2me | Theorems.Thm_DynOpaque_TwoPeriod_case_vHL_vL_dominated
-- name    : DynOpaque.TwoPeriod.case_vHL_vL_dominated
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:22:21.705385+00:00
-- url     : https://prove2.me/theorems/3c8b5dec-00dd-4f0e-b0ca-ecd2e3e5b0ea
-- title:
--   Proof of Proposition 1, p. 30 — the price pair p1 = vHL, p2 = vL is never optimal
-- statement:
--   Assume $v_H>v_L$, $c_H>c_L$, $0\le\alpha\le1$, $c_L\le v_L$. For every $(\xi_1,\xi_2)\in[0,1]^2$ there is $(\xi_1',\xi_2')\in[0,1]^2$ with
--   $$
--   \Pi(\xi_1,\xi_2\mid v_{HL},v_L)\ \le\ \max\bigl\{\Pi(\xi_1',\xi_2'\mid v_{HL},v_{HL}),\ 2\max\{v_H-c_H,\ v_L-c_L\}\bigr\},
--   $$
--   where the left side is objective (4) and $\Pi(\cdot\mid v_{HL},v_{HL})$ is objective (3).
--
--   In words: whatever the firm earns with the price pair $(v_{HL},v_L)$, it earns at least as much either with $(v_{HL},v_{HL})$ or with the best transparent policy. This is the first step of the paper's proof of Proposition 1.
--
--   **Formalization Note** "Never optimal" is formalized as weak domination; at boundary parameter values the two sides can be equal.
-- source:
--   Huang and Yin, Dynamic Probabilistic Selling When Customers Have Boundedly Rational Expectations, SSRN manuscript 3627927, p. 30, proof of Proposition 1, first paragraph

import Mathlib
import Definitions.Def_DynOpaque_TwoPeriod_Model

namespace DynOpaque.TwoPeriod

/-- Proof of Proposition 1, p. 30: the case `p₁ = vHL`, `p₂ = vL` is never optimal — every
value of objective (4) on the box is at most the larger of some value of objective (3) on the box
and the best transparent profit `2 max{vH − cH, vL − cL}`. -/
theorem case_vHL_vL_dominated (vH vL cH cL α : ℝ) (hS : Standing vH vL cH cL α) :
    ∀ x ∈ box, ∃ y ∈ box,
      obj4 vH vL cH cL x.1 x.2 ≤ max (obj3 vH vL cH cL α y.1 y.2) (2 * max (vH - cH) (vL - cL)) := by sorry

end DynOpaque.TwoPeriod
