-- Prove2me | Theorems.Thm_DynOpaque_TwoPeriod_objectives_3_to_6
-- name    : DynOpaque.TwoPeriod.objectives_3_to_6
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:22:15.7634+00:00
-- url     : https://prove2.me/theorems/13a91190-6df4-4be6-8d5c-26986461c7ab
-- title:
--   Eqs. (3)–(6), pp. 11–13 — at the four candidate price pairs, profit (2) equals the printed objectives (3)–(6)
-- statement:
--   Assume the standing assumptions $v_H>v_L$, $c_H>c_L$, $0\le\alpha\le1$, $c_L\le v_L$, and let $\xi_1,\xi_2$ be real numbers. Write $\Pi(\xi_1,\xi_2\mid p_1,p_2)$ for the profit (2) computed from the one-anecdote purchase rule. Then
--   $$
--   \begin{aligned}
--   \Pi(\xi_1,\xi_2\mid v_{HL},v_{HL})&=\xi_1[v_{HL}-\xi_1c_H-(1-\xi_1)c_L]+[\alpha\xi_1+(1-\alpha)\xi_2][v_{HL}-\xi_2c_H-(1-\xi_2)c_L], &(3)\\
--   \Pi(\xi_1,\xi_2\mid v_{HL},v_L)&=\xi_1[v_{HL}-\xi_1c_H-(1-\xi_1)c_L]+[v_L-\xi_2c_H-(1-\xi_2)c_L], &(4)\\
--   \Pi(\xi_1,\xi_2\mid v_L,v_{HL})&=[v_L-\xi_1c_H-(1-\xi_1)c_L]+[\alpha\xi_1+(1-\alpha)\xi_2][v_{HL}-\xi_2c_H-(1-\xi_2)c_L], &(5)\\
--   \Pi(\xi_1,\xi_2\mid v_L,v_L)&=[v_L-\xi_1c_H-(1-\xi_1)c_L]+[v_L-\xi_2c_H-(1-\xi_2)c_L]. &(6)
--   \end{aligned}
--   $$
--
--   These identities are how §4 rewrites the firm's problem (2) for each of the four candidate price pairs; Lemmas 2–4 and the claim after (6) then optimize the right-hand sides.
--
--   **Formalization Note** The right-hand sides are separate definitions written literally from the page, so the identities are not true by definition.
-- source:
--   Huang and Yin, Dynamic Probabilistic Selling When Customers Have Boundedly Rational Expectations, SSRN manuscript 3627927, pp. 11–13, eqs. (3), (4), (5), (6)

import Mathlib
import Definitions.Def_DynOpaque_TwoPeriod_Model

namespace DynOpaque.TwoPeriod

/-- Displays (3)–(6), pp. 11–13: at the four candidate price pairs, profit (2) is the
objective printed for that pair. -/
theorem objectives_3_to_6 (vH vL cH cL α : ℝ) (hS : Standing vH vL cH cL α) (ξ₁ ξ₂ : ℝ) :
    opaqueProfit vH vL cH cL α (vHL vH vL) (vHL vH vL) ξ₁ ξ₂ = obj3 vH vL cH cL α ξ₁ ξ₂ ∧
    opaqueProfit vH vL cH cL α (vHL vH vL) vL ξ₁ ξ₂ = obj4 vH vL cH cL ξ₁ ξ₂ ∧
    opaqueProfit vH vL cH cL α vL (vHL vH vL) ξ₁ ξ₂ = obj5 vH vL cH cL α ξ₁ ξ₂ ∧
    opaqueProfit vH vL cH cL α vL vL ξ₁ ξ₂ = obj6 vL cH cL ξ₁ ξ₂ := by sorry

end DynOpaque.TwoPeriod
