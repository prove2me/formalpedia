-- Prove2me | Theorems.Thm_ChoiceRM_FareOrder_theorem_2
-- name    : ChoiceRM.FareOrder.theorem_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T15:46:22.618589+00:00
-- url     : https://prove2.me/theorems/c5980f75-c8f0-4181-8464-0abf496e2a32
-- title:
--   Theorem 2, p. 19 — nesting by fare order iff Q is increasing and a mixture of complete sets majorizes every incomplete set
-- statement:
--   Throughout, $N = \{1, \dots, n\}$ is the set of fare products, indexed in fare order $r_1 \ge r_2 \ge \dots \ge r_n \ge 0$. A **choice model** assigns to every offer set $S \subseteq N$ and product $j$ a purchase probability $P_j(S) \ge 0$, with $P_j(S) = 0$ for $j \notin S$ and $Q(S) = \sum_{j \in S} P_j(S) \le 1$ (the no-purchase probability is $P_0(S) = 1 - Q(S)$). The **complete sets** are $A_k = \{1, \dots, k\}$ for $k = 0, 1, \dots, n$, with $A_0 = \emptyset$; every other set is **incomplete**.
--
--   The choice model has the **nesting-by-fare-order property** (Definition 4) if $Q$ is increasing ($Q(S) \le Q(T)$ for $S \subseteq T$) and, for every $x_1 \ge x_2 \ge \dots \ge x_n$, the problem $\max_{S \subseteq N} \sum_{j=1}^n x_j P_j(S)$ has a complete optimal solution.
--
--   **Theorem 2.** The choice model has the nesting-by-fare-order property if and only if
--
--   1. the probability of purchase $Q(S)$ is increasing in $S$, and
--
--   2. for every incomplete set $T$ there are convex weights $\alpha_0, \dots, \alpha_n \ge 0$, $\sum_k \alpha_k = 1$, such that the probabilities $\bar P_j(\alpha) = \sum_{k=0}^n \alpha_k P_j(A_k)$ satisfy
--
--   $$\sum_{j=1}^i \bar P_j(\alpha) \ge \sum_{j=1}^i P_j(T) \quad (i = 1, \dots, n-1) \qquad\text{and}\qquad \sum_{j=1}^n \bar P_j(\alpha) = \sum_{j=1}^n P_j(T).$$
--
--   In the language of majorization, the vector $(\bar P_1(\alpha), \dots, \bar P_n(\alpha))$ majorizes $(P_1(T), \dots, P_n(T))$ in fare order. The theorem reduces the question whether an optimal revenue-management policy is nested by fare order to a finite family of linear feasibility problems, one per incomplete set, and is the tool the paper uses for the independent-demand and multinomial-logit models.
--
--   **Formalization Note** Fare $j \in \{1, \dots, n\}$ is the element $j - 1$ of `Fin n`; the order $x_1 \ge \dots \ge x_n$ is `Antitone x`; $A_k$ is `complete n k`; the choice-model axioms are `IsChoiceModel P` (platform definition `RevenueManagement_singleResource`) together with `SupportedOn P` ($P_j(S) = 0$ off $S$, the model's own convention on p. 5). The page writes $\bar P_j(\alpha) = \sum_{k=1}^n \alpha_k P_j(S_k)$; $S_k$ is the complete set $A_k$ (a printed slip, as the proof on p. 20 shows). Complete sets are indexed by $k \in \{0, \dots, n\}$, so $A_0 = \emptyset$ counts as complete and the weights $\alpha$ live on $n + 1$ sets. The page indexes the weights by $k = 1, \dots, n$; the paper notes on p. 21 that Theorem 2 holds for any specified family of sets, and with $A_0$ included the property is the one the paper's Propositions 5 and 6 need (for MNL and all $x_j < 0$, the unique optimum of (9) is $\emptyset$). The prefix condition is stated for $i = 0, \dots, n-1$; $i = 0$ is trivially true.
-- source:
--   Talluri, van Ryzin, Revenue management under a general discrete choice model of consumer behavior, working paper of October 21, 2001 (UPF Economics Working Paper 533; published Management Science 50(1), 2004, DOI 10.1287/mnsc.1030.0147), p. 19, Theorem 2 (with Definition 4, p. 18)

import Mathlib
import Definitions.Def_RevenueManagement_singleResource
import Definitions.Def_ChoiceRM_FareOrder_FareOrder

namespace ChoiceRM.FareOrder

open RevenueManagement

/-- Theorem 2, p. 19: a choice model has the nested-by-fare-order property iff (i) the purchase
probability `Q` is increasing and (ii) for every incomplete set `T` some convex combination
`P̄(α)` of the complete sets majorizes `(P_1(T), …, P_n(T))`. -/
theorem theorem_2 {n : ℕ} (P : Finset (Fin n) → Fin n → ℝ)
    (hP : IsChoiceModel P) (hsupp : SupportedOn P) :
    HasFareOrderNesting P ↔
      ((∀ S T : Finset (Fin n), S ⊆ T → purchaseProb P S ≤ purchaseProb P T) ∧
        ∀ T : Finset (Fin n), ¬ IsComplete T →
          ∃ α : Fin (n + 1) → ℝ, (∀ k, 0 ≤ α k) ∧ ∑ k, α k = 1 ∧
            (∀ i, i < n → ∑ j ∈ complete n i, P T j ≤ ∑ j ∈ complete n i, mixProb P α j) ∧
            ∑ j, mixProb P α j = ∑ j, P T j) := by sorry

end ChoiceRM.FareOrder
