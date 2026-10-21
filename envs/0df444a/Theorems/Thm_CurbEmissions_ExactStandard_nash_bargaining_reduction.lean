-- Prove2me | Theorems.Thm_CurbEmissions_ExactStandard_nash_bargaining_reduction
-- name    : CurbEmissions.ExactStandard.nash_bargaining_reduction
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:18:19.458191+00:00
-- url     : https://prove2.me/theorems/0fcc08c0-8166-42e0-be74-9ac4e3af1a7a
-- title:
--   §4.1.1, p. 19 — a Nash bargaining solution maximizes total utility Th and exceeds the split-market total
-- statement:
--   Let the standing assumptions hold and let $(D_1,D_2)$ be any disagreement point. Suppose some exact global standard $s\ge0$ gives the regulators a total utility $T_h(s)>D_1+D_2$. Then the Nash bargaining solutions of the exact-standard negotiation are exactly the pairs $(s_e,t_h)$ such that
--   1. $s_e\ge0$ maximizes the total utility over all exact global standards, $T_h(s)\le T_h(s_e)$ for every $s\ge0$, and
--   2. the transfer splits the gain equally, $\Pi_1(s_e,t_h)-D_1=\Pi_2(s_e,t_h)-D_2$.
--
--   Moreover, at every Nash bargaining solution
--   $$T_h(s_e)>D_1+D_2 .$$
--
--   This reduces the negotiation to the maximization of $T_h$, which is the arbitrator's problem (3), plus the comparison of the maximum with the split-market total.
--
--   **Formalization Note** The page assumes a non-empty feasibility set; the condition "the total exceeds that at the split-market outcome" requires the strict inequality $T_h(s)>D_1+D_2$ for some $s$, which is the hypothesis used here.
-- source:
--   Han, Hu & Dawande, Curbing Emissions: Environmental Regulations and Product Offerings Across Markets, MSOM (authors' accepted manuscript, 2022-07-28), p. 19, §4.1.1 (unnumbered claim following eq. (5))

import Mathlib
import Definitions.Def_CurbEmissions_ExactStandard_Model

namespace CurbEmissions.ExactStandard

/-- §4.1.1, p. 19: when some exact standard gives the regulators more than `D1 + D2` in total, the Nash
bargaining solutions are exactly the pairs `(se, th)` whose standard maximizes `T_h` over `se ≥ 0` and
whose transfer splits the gain equally; at every such solution the total exceeds `D1 + D2`. -/
theorem nash_bargaining_reduction (P : Params) (hP : Standing P) (D1 D2 : ℝ)
    (hgain : ∃ s, 0 ≤ s ∧ D1 + D2 < Th P s) :
    NBS P D1 D2 =
      {q | 0 ≤ q.1 ∧ (∀ s, 0 ≤ s → Th P s ≤ Th P q.1) ∧
           Pi1 P q.1 q.2 - D1 = Pi2 P q.1 q.2 - D2} ∧
    ∀ q ∈ NBS P D1 D2, D1 + D2 < Th P q.1 := by sorry

end CurbEmissions.ExactStandard
