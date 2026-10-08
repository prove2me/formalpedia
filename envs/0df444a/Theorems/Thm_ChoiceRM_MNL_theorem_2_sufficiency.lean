-- Prove2me | Theorems.Thm_ChoiceRM_MNL_theorem_2_sufficiency
-- name    : ChoiceRM.MNL.theorem_2_sufficiency
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:47:58.485905+00:00
-- url     : https://prove2.me/theorems/433d6b06-02ed-4d4b-a6e0-464f18b0869b
-- title:
--   Theorem 2 (⇐), p. 19 — increasing Q and majorizing mixtures of complete sets give nesting by fare order
-- statement:
--   Let $P_j(S)$ be a choice model on $N = \{1, \dots, n\}$: $P_j(S) \ge 0$, $\sum_{j \in S} P_j(S) \le 1$, and $P_j(S) = 0$ for $j \notin S$. Suppose
--
--   1. the purchase probability $Q(S) = \sum_{j\in S} P_j(S)$ is increasing: $Q(S) \le Q(T)$ whenever $S \subseteq T$; and
--   2. for every incomplete set $T$ there are convex weights $\alpha_0, \dots, \alpha_n \ge 0$, $\sum_k \alpha_k = 1$, such that $\bar P_j(\alpha) = \sum_{k} \alpha_k P_j(A_k)$ satisfies
--   $$
--   \sum_{j=1}^{i} \bar P_j(\alpha) \ge \sum_{j=1}^{i} P_j(T), \quad i = 1, \dots, n-1, \qquad \sum_{j=1}^{n} \bar P_j(\alpha) = \sum_{j=1}^{n} P_j(T).
--   $$
--
--   Then the choice model has the nesting-by-fare-order property (Definition 4).
--
--   This is the direction of Theorem 2 used to establish nesting by fare order for specific models such as the independent and MNL models.
--
--   **Formalization Note** This is one direction of Theorem 2, the goal of mission 2 of this series, restated here because draft items cannot import other missions' drafts; its hypotheses are copied from that statement. The weights are indexed by $k \in \{0, \dots, n\}$, with $A_0 = \emptyset$ (the page writes $k = 1, \dots, n$ and $S_k$ for $A_k$). The prefix condition is stated for $i = 0, \dots, n-1$; the case $i = 0$ is trivial. `SupportedOn P` is the model's convention $P_j(S) = 0$ for $j \notin S$ (§1, p. 5), needed because $\bar P$ and the totals sum over all products.
-- source:
--   Talluri, van Ryzin, Revenue management under a general discrete choice model of consumer behavior, working paper of October 21, 2001 (UPF Economics Working Paper 533; published Management Science 50(1), 2004, DOI 10.1287/mnsc.1030.0147), p. 19, Theorem 2 (sufficiency direction)

import Mathlib
import Definitions.Def_RevenueManagement_singleResource
import Definitions.Def_ChoiceRM_MNL_FareOrder

namespace ChoiceRM.MNL

open RevenueManagement

/-- Theorem 2 (⇐), p. 19: if (i) the purchase probability `Q` is increasing and (ii) for every
incomplete set `T` some convex combination `P̄(α)` of the complete sets majorizes
`(P_1(T), …, P_n(T))`, then the choice model has the nested-by-fare-order property. -/
theorem theorem_2_sufficiency {n : ℕ} (P : Finset (Fin n) → Fin n → ℝ)
    (hP : IsChoiceModel P) (hsupp : SupportedOn P)
    (hi : ∀ S T : Finset (Fin n), S ⊆ T → purchaseProb P S ≤ purchaseProb P T)
    (hii : ∀ T : Finset (Fin n), ¬ IsComplete T →
      ∃ α : Fin (n + 1) → ℝ, (∀ k, 0 ≤ α k) ∧ ∑ k, α k = 1 ∧
        (∀ i, i < n → ∑ j ∈ complete n i, P T j ≤ ∑ j ∈ complete n i, mixProb P α j) ∧
        ∑ j, mixProb P α j = ∑ j, P T j) :
    HasFareOrderNesting P := by sorry

end ChoiceRM.MNL
