-- Prove2me | Theorems.Thm_DeferredInspection_SingleAgent_proposition_2
-- name    : DeferredInspection.SingleAgent.proposition_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T04:58:13.028822+00:00
-- url     : https://prove2.me/theorems/9c325667-8a8f-479a-ac86-a3f5dfd676b2
-- title:
--   Proposition 2, p. 7 — greatest incentive-compatible payment
-- statement:
--   Fix an allocation probability $x:V\to[0,1]$. Its **optimal payment rule** is
--
--   $$p_x(v)=\inf_{0\le w\le v}\{v(x(v)-x(w))+w\}.$$
--
--   Every incentive-compatible payment rule for $x$ is at most $p_x$ at every value. If $x(0)=0$, then $(x,p_x)$ itself satisfies incentive compatibility and individual rationality. Thus $p_x$ is the greatest feasible payment for this fixed allocation.
--
--   **Formalization Note** This is the pointwise improvement statement established by the proof. The page's claim that every optimal mechanism uses this payment pointwise can fail after changing its payment on a null set.
-- source:
--   Alaei, Belloni, Makhdoumi & Malekian, SSRN 3700525 (version of 2022-03-22), p. 7, Proposition 2 and (10); proof pp. 27–28

import Mathlib
import Definitions.Def_DeferredInspection_SingleAgent_Model

namespace DeferredInspection.SingleAgent

open MeasureTheory Set Filter Topology

theorem proposition_2 (x p : ℝ → ℝ) (hx : IsAllocation x) :
    (IsIC x p → ∀ v ∈ Icc (0 : ℝ) 1, p v ≤ optPay x v) ∧
    (x 0 = 0 → IsIC x (optPay x) ∧ IsIR x (optPay x)) := by sorry

end DeferredInspection.SingleAgent
