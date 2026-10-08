-- Prove2me | Theorems.Thm_ChoiceRM_FareOrder_dual_iff_majorization
-- name    : ChoiceRM.FareOrder.dual_iff_majorization
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:48:59.741781+00:00
-- url     : https://prove2.me/theorems/5b8c8578-abef-4485-b758-614cb8bab825
-- title:
--   Proof of Theorem 2, pp. 20–21 — eliminating z: the dual system is solvable iff P̄(α) majorizes P(T)
-- statement:
--   Throughout, $N = \{1, \dots, n\}$ is the set of fare products, indexed in fare order $r_1 \ge r_2 \ge \dots \ge r_n \ge 0$. A **choice model** assigns to every offer set $S \subseteq N$ and product $j$ a purchase probability $P_j(S) \ge 0$, with $P_j(S) = 0$ for $j \notin S$ and $Q(S) = \sum_{j \in S} P_j(S) \le 1$ (the no-purchase probability is $P_0(S) = 1 - Q(S)$). The **complete sets** are $A_k = \{1, \dots, k\}$ for $k = 0, 1, \dots, n$, with $A_0 = \emptyset$; every other set is **incomplete**.
--
--   Let $T \subseteq N$. The dual system — $\alpha_0, \dots, \alpha_n \ge 0$ with $\sum_k \alpha_k = 1$ and $z_0, \dots, z_n \ge 0$ with $z_0 = z_n = 0$ and $\bar P_j(\alpha) - z_j + z_{j-1} = P_j(T)$ for $j = 1, \dots, n$, where $\bar P_j(\alpha) = \sum_{k=0}^n \alpha_k P_j(A_k)$ — is solvable if and only if there are weights $\alpha_0, \dots, \alpha_n \ge 0$ with $\sum_k \alpha_k = 1$ such that
--
--   $$\sum_{j=1}^i \bar P_j(\alpha) \ge \sum_{j=1}^i P_j(T) \quad (i = 1, \dots, n-1) \qquad\text{and}\qquad \sum_{j=1}^n \bar P_j(\alpha) = \sum_{j=1}^n P_j(T).$$
--
--   This step removes the auxiliary variables $z$ and leaves exactly the majorization condition (ii) of Theorem 2.
--
--   **Formalization Note** Fare $j \in \{1, \dots, n\}$ is the element $j - 1$ of `Fin n`; the order $x_1 \ge \dots \ge x_n$ is `Antitone x`; $A_k$ is `complete n k`; the choice-model axioms are `IsChoiceModel P` (platform definition `RevenueManagement_singleResource`) together with `SupportedOn P` ($P_j(S) = 0$ off $S$, the model's own convention on p. 5). The prefix condition is stated for $i = 0, 1, \dots, n-1$ ($\sum_{j \in A_i}$, with $i = 0$ trivially true); the total uses all $n$ products. Complete sets are indexed by $k \in \{0, \dots, n\}$, so $A_0 = \emptyset$ counts as complete and the weights $\alpha$ live on $n + 1$ sets. The page indexes the weights by $k = 1, \dots, n$; the paper notes on p. 21 that Theorem 2 holds for any specified family of sets, and with $A_0$ included the property is the one the paper's Propositions 5 and 6 need (for MNL and all $x_j < 0$, the unique optimum of (9) is $\emptyset$).
-- source:
--   Talluri, van Ryzin, Revenue management under a general discrete choice model of consumer behavior, working paper of October 21, 2001 (UPF Economics Working Paper 533; published Management Science 50(1), 2004, DOI 10.1287/mnsc.1030.0147), pp. 20–21, proof of Theorem 2 ("We can next eliminate the z variables")

import Mathlib
import Definitions.Def_RevenueManagement_singleResource
import Definitions.Def_ChoiceRM_FareOrder_FareOrder
import Definitions.Def_ChoiceRM_FareOrder_Systems

namespace ChoiceRM.FareOrder

open RevenueManagement

/-- Proof of Theorem 2, pp. 20–21: eliminating `z`, the dual system is solvable iff some convex
weights on the complete sets give prefix sums of `P̄(α)` at least those of `P(T)` and the same
total. -/
theorem dual_iff_majorization {n : ℕ} (P : Finset (Fin n) → Fin n → ℝ)
    (hP : IsChoiceModel P) (hsupp : SupportedOn P) (T : Finset (Fin n)) :
    DualSolvable P T ↔
      ∃ α : Fin (n + 1) → ℝ, (∀ k, 0 ≤ α k) ∧ ∑ k, α k = 1 ∧
        (∀ i, i < n → ∑ j ∈ complete n i, P T j ≤ ∑ j ∈ complete n i, mixProb P α j) ∧
        ∑ j, mixProb P α j = ∑ j, P T j := by sorry

end ChoiceRM.FareOrder
