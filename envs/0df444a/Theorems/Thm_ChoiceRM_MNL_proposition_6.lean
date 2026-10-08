-- Prove2me | Theorems.Thm_ChoiceRM_MNL_proposition_6
-- name    : ChoiceRM.MNL.proposition_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:52:05.507309+00:00
-- url     : https://prove2.me/theorems/5b20e2b3-e486-45d3-9764-78aa400c8d63
-- title:
--   Proposition 6, p. 23 — the MNL choice model has the nesting-by-fare-order property
-- statement:
--   Let $w_1, \dots, w_n > 0$ be MNL preference weights (with no-purchase weight $w_0 = 1$), and let
--   $$
--   P_j(S) = \frac{w_j}{\sum_{i\in S} w_i + 1}, \quad j \in S, \qquad P_j(S) = 0, \quad j \notin S,
--   $$
--   be the MNL choice probabilities (14). Then this choice model has the nesting-by-fare-order property (Definition 4):
--
--   1. the purchase probability $Q(S) = \sum_{j \in S} P_j(S)$ is increasing in $S$; and
--   2. for all values $x_1 \ge x_2 \ge \dots \ge x_n$, the problem $\max_{S \subseteq N} \sum_{j} x_j P_j(S)$ has an optimal solution that is a complete set $A_k = \{1, \dots, k\}$, $0 \le k \le n$.
--
--   By the theory of §§2–3 of the paper, this means that under MNL demand the optimal single-resource revenue management policy opens fares in fare order: a convex combination of the two complete sets $A_{k^*}$ and $A_{k^*+1}$ dominates any incomplete set.
--
--   **Formalization Note** The paper states Proposition 6 as "the only nondominated sets are the complete sets $A_k$, $k = 1, \dots, n$. Moreover, the optimal policy is a nested allocation policy where the nesting is by fare order." This item states what the proof (pp. 24–25) establishes, the two conditions of Theorem 2 / Definition 4. The literal first sentence is false when fares tie: with $r_1 = r_2 > 0$ and $w_1 = w_2$, the incomplete set $\{2\}$ is nondominated; it is stated separately as `proposition_6_nondominated_complete` under strictly decreasing fares. The "Moreover" sentence about nested allocation policies (Definition 3) is not formalized. The empty set $A_0$ counts as complete; without it, condition 2 fails whenever all $x_j < 0$.
-- source:
--   Talluri, van Ryzin, Revenue management under a general discrete choice model of consumer behavior, working paper of October 21, 2001 (UPF Economics Working Paper 533; published Management Science 50(1), 2004, DOI 10.1287/mnsc.1030.0147), p. 23, Proposition 6 (proof pp. 24–25)

import Mathlib
import Definitions.Def_RevenueManagement_singleResource
import Definitions.Def_ChoiceRM_MNL_FareOrder
import Definitions.Def_ChoiceRM_MNL_Models

namespace ChoiceRM.MNL

/-- Proposition 6, p. 23, in the form its proof establishes (pp. 24–25): the MNL choice model (14)
with positive weights has the nesting-by-fare-order property of Definition 4. -/
theorem proposition_6 {n : ℕ} (w : Fin n → ℝ) (hw : ∀ j, 0 < w j) :
    HasFareOrderNesting (mnl w) := by sorry

end ChoiceRM.MNL
