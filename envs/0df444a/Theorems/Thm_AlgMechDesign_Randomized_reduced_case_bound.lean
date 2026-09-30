-- Prove2me | Theorems.Thm_AlgMechDesign_Randomized_reduced_case_bound
-- name    : AlgMechDesign.Randomized.reduced_case_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T20:44:03.800271+00:00
-- url     : https://prove2.me/theorems/06e91a9f-119e-4082-b969-f0449904979e
-- title:
--   Lemma 4.18, reduced case (Fig. 2, Cases 1–3) — expected make-span at most 7/4 · t_opt
-- statement:
--   Let $\beta = 4/3$ and $a, b, c, d \ge 0$. Consider the four-task instance of Fig. 2 for two agents: task $k_1$ with times $(a, \beta a)$, $k_2$ with $(b, \beta b)$, $l_1$ with $(c, \beta c)$ and $l_2$ with $(\beta d, d)$ for agents $(1, 2)$. The mechanism gives $k_1, k_2$ to agent 1 and gives each of $l_1, l_2$ to either agent with probability $1/2$; the optimal allocation gives $k_1, l_1$ to agent 1 and $k_2, l_2$ to agent 2. If both agents finish at the same time under the optimal allocation, $t_{opt} = a + c = \beta b + d$, then the expected make-span over the four equally likely allocations satisfies
--   $$
--   t_{bmw} = \tfrac14\Big(\max(a+b+c+\beta d,\ 0) + \max(a+b+c,\ d) + \max(a+b+\beta d,\ \beta c) + \max(a+b,\ \beta c + d)\Big) \le \tfrac74 (a + c).
--   $$
--
--   This is the case to which the paper reduces Lemma 4.18; zero times represent instances with fewer than four tasks.
--
--   **Formalization Note** The three cases of the paper are combined into one inequality with explicit maxima, with $\beta = 4/3$ substituted.
-- source:
--   Nisan, Ronen, Algorithmic Mechanism Design, Games Econ. Behav. 35, 2001, pp. 184–185, proof of Lemma 4.18, Fig. 2 and Cases 1–3

import Mathlib

namespace AlgMechDesign.Randomized

/-- The reduced case of Lemma 4.18 (Fig. 2, Cases 1–3, pp. 184–185), with `β = 4/3`: tasks
`k₁, k₂` (times `(a, βa)` and `(b, βb)`) go to agent 1, while `l₁` (times `(c, βc)`) and `l₂`
(times `(βd, d)`) are each allocated to either agent with probability `1/2`. If opt's two
finishing times agree, `a + c = βb + d`, the expected make-span is at most `7/4 · (a + c)`. -/
theorem reduced_case_bound (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hopt : a + c = 4 / 3 * b + d) :
    (1 / 4 : ℝ) * (max (a + b + c + 4 / 3 * d) 0 + max (a + b + c) d +
        max (a + b + 4 / 3 * d) (4 / 3 * c) + max (a + b) (4 / 3 * c + d)) ≤
      7 / 4 * (a + c) := by sorry

end AlgMechDesign.Randomized
