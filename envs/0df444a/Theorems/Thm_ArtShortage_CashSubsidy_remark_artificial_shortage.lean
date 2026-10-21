-- Prove2me | Theorems.Thm_ArtShortage_CashSubsidy_remark_artificial_shortage
-- name    : ArtShortage.CashSubsidy.remark_artificial_shortage
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:23:56.392986+00:00
-- url     : https://prove2.me/theorems/7837d8bf-18f4-42e7-9264-be9fe34bd8f3
-- title:
--   §3, p. 10, remark after Proposition 1 — for g > 0 the no-intervention optimum is an artificial shortage (Definition 1)
-- statement:
--   Under no intervention, with $0<g<4$ and $1+g<\lambda$, the trader's total revenue $q_1(1-q_1)+(1+g(1-q_1))q_2(1-q_2)$ attains its maximum on $[0,1]^2$. Every maximizer $(q_1^*,q_2^*)$, with prices $p_1^*=1-q_1^*$ and $p_2^*=(1-q_2^*)(1+g(1-q_1^*))$, satisfies
--   $$q_1^*<q_2^*\quad\text{and}\quad p_1^*<p_2^* .$$
--   That is, the trader creates an artificial shortage in the sense of Definition 1: he sells more in Period 2 at a higher price.
--
--   This is the paper's motivating observation: the supply–price relation is reversed whenever consumers raise their budgets in response to scarcity.
-- source:
--   Levi, Singhvi & Zheng, Artificial Shortage in Agricultural Supply Chains, SSRN 3332493 (version of 2021-04-14; MSOM forthcoming), p. 10, §3, remark after Proposition 1; p. 9, Definition 1

import Mathlib
import Definitions.Def_ArtShortage_CashSubsidy_Model

namespace ArtShortage.CashSubsidy

theorem remark_artificial_shortage (g lam : ℝ) (hS : Standing g lam) :
    (∃ q1 q2, IsNoIntOpt g q1 q2) ∧
      ∀ q1 q2, IsNoIntOpt g q1 q2 → IsArtificialShortage q1 (p1 q1) q2 (p2NoInt g q1 q2) := by sorry

end ArtShortage.CashSubsidy
