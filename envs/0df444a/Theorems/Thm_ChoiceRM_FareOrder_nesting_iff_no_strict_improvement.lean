-- Prove2me | Theorems.Thm_ChoiceRM_FareOrder_nesting_iff_no_strict_improvement
-- name    : ChoiceRM.FareOrder.nesting_iff_no_strict_improvement
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:51:26.403869+00:00
-- url     : https://prove2.me/theorems/6d01a341-79f2-4f42-84f4-5bfdd35b97c0
-- title:
--   Proof of Theorem 2, p. 20 — Definition 4(ii) holds iff (10)–(11) has no solution for every incomplete T
-- statement:
--   Throughout, $N = \{1, \dots, n\}$ is the set of fare products, indexed in fare order $r_1 \ge r_2 \ge \dots \ge r_n \ge 0$. A **choice model** assigns to every offer set $S \subseteq N$ and product $j$ a purchase probability $P_j(S) \ge 0$, with $P_j(S) = 0$ for $j \notin S$ and $Q(S) = \sum_{j \in S} P_j(S) \le 1$ (the no-purchase probability is $P_0(S) = 1 - Q(S)$). The **complete sets** are $A_k = \{1, \dots, k\}$ for $k = 0, 1, \dots, n$, with $A_0 = \emptyset$; every other set is **incomplete**.
--
--   Then the following are equivalent.
--
--   1. For every $x_1 \ge x_2 \ge \dots \ge x_n$, problem (9), $\max_{S \subseteq N} \sum_{j \in S} x_j P_j(S)$, has an optimal solution that is a complete set $A_k$, $0 \le k \le n$ (condition (ii) of Definition 4).
--
--   2. For every incomplete set $T$, the linear system (10)–(11) in the variables $x$ and $u$ has no solution: there are no $x_1 \ge \dots \ge x_n$ and $u$ with
--
--   $$u < \sum_{j \in T} x_j P_j(T), \qquad \sum_{j \in A_k} x_j P_j(A_k) \le u \quad (k = 0, \dots, n).$$
--
--   This is the first step of the proof of Theorem 2: it turns the optimization property of Definition 4(ii) into the infeasibility of one linear system per incomplete set, to which Farkas' lemma applies.
--
--   **Formalization Note** Fare $j \in \{1, \dots, n\}$ is the element $j - 1$ of `Fin n`; the order $x_1 \ge \dots \ge x_n$ is `Antitone x`; $A_k$ is `complete n k`; the choice-model axioms are `IsChoiceModel P` (platform definition `RevenueManagement_singleResource`) together with `SupportedOn P` ($P_j(S) = 0$ off $S$, the model's own convention on p. 5). Complete sets are indexed by $k \in \{0, \dots, n\}$, so $A_0 = \emptyset$ counts as complete and the weights $\alpha$ live on $n + 1$ sets. The page indexes the weights by $k = 1, \dots, n$; the paper notes on p. 21 that Theorem 2 holds for any specified family of sets, and with $A_0$ included the property is the one the paper's Propositions 5 and 6 need (for MNL and all $x_j < 0$, the unique optimum of (9) is $\emptyset$).
-- source:
--   Talluri, van Ryzin, Revenue management under a general discrete choice model of consumer behavior, working paper of October 21, 2001 (UPF Economics Working Paper 533; published Management Science 50(1), 2004, DOI 10.1287/mnsc.1030.0147), p. 20, proof of Theorem 2 (Part ii), eqs. (10)–(11); converse closed on p. 21 ("if and only if")

import Mathlib
import Definitions.Def_RevenueManagement_singleResource
import Definitions.Def_ChoiceRM_FareOrder_FareOrder
import Definitions.Def_ChoiceRM_FareOrder_Systems

namespace ChoiceRM.FareOrder

open RevenueManagement

/-- Proof of Theorem 2, p. 20: condition (ii) of Definition 4 holds iff, for every incomplete
set `T`, the system (10)–(11) has no solution. -/
theorem nesting_iff_no_strict_improvement {n : ℕ} (P : Finset (Fin n) → Fin n → ℝ)
    (hP : IsChoiceModel P) (hsupp : SupportedOn P) :
    (∀ x : Fin n → ℝ, Antitone x →
        ∃ k ≤ n, ∀ S : Finset (Fin n), fareValue P x S ≤ fareValue P x (complete n k)) ↔
      ∀ T : Finset (Fin n), ¬ IsComplete T → NoStrictImprovement P T := by sorry

end ChoiceRM.FareOrder
