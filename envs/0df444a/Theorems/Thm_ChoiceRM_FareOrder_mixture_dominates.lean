-- Prove2me | Theorems.Thm_ChoiceRM_FareOrder_mixture_dominates
-- name    : ChoiceRM.FareOrder.mixture_dominates
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:46:42.000005+00:00
-- url     : https://prove2.me/theorems/293394f6-a551-41c9-9228-96ed1b808884
-- title:
--   pp. 19–20, after Theorem 2 — a majorizing mixture of complete sets earns at least as much as T
-- statement:
--   Throughout, $N = \{1, \dots, n\}$ is the set of fare products, indexed in fare order $r_1 \ge r_2 \ge \dots \ge r_n \ge 0$. A **choice model** assigns to every offer set $S \subseteq N$ and product $j$ a purchase probability $P_j(S) \ge 0$, with $P_j(S) = 0$ for $j \notin S$ and $Q(S) = \sum_{j \in S} P_j(S) \le 1$ (the no-purchase probability is $P_0(S) = 1 - Q(S)$). The **complete sets** are $A_k = \{1, \dots, k\}$ for $k = 0, 1, \dots, n$, with $A_0 = \emptyset$; every other set is **incomplete**.
--
--   Let $T \subseteq N$ and let $\alpha_0, \dots, \alpha_n \ge 0$ with $\sum_k \alpha_k = 1$ be weights such that $\bar P_j(\alpha) = \sum_{k=0}^n \alpha_k P_j(A_k)$ satisfies
--
--   $$\sum_{j=1}^i \bar P_j(\alpha) \ge \sum_{j=1}^i P_j(T) \quad (i = 1, \dots, n-1), \qquad \sum_{j=1}^n \bar P_j(\alpha) = \sum_{j=1}^n P_j(T).$$
--
--   Then for every $x_1 \ge x_2 \ge \dots \ge x_n$,
--
--   $$\sum_{j \in T} x_j P_j(T) \;\le\; \sum_{k=0}^n \alpha_k \sum_{j \in A_k} x_j P_j(A_k).$$
--
--   This is the paper's direct explanation of why the majorization condition suffices: the convex combination of complete sets produces at least as much value in (9) as $T$, for the same probability of purchase.
--
--   **Formalization Note** Fare $j \in \{1, \dots, n\}$ is the element $j - 1$ of `Fin n`; the order $x_1 \ge \dots \ge x_n$ is `Antitone x`; $A_k$ is `complete n k`; the choice-model axioms are `IsChoiceModel P` (platform definition `RevenueManagement_singleResource`) together with `SupportedOn P` ($P_j(S) = 0$ off $S$, the model's own convention on p. 5). Complete sets are indexed by $k \in \{0, \dots, n\}$, so $A_0 = \emptyset$ counts as complete and the weights $\alpha$ live on $n + 1$ sets. The page indexes the weights by $k = 1, \dots, n$; the paper notes on p. 21 that Theorem 2 holds for any specified family of sets, and with $A_0$ included the property is the one the paper's Propositions 5 and 6 need (for MNL and all $x_j < 0$, the unique optimum of (9) is $\emptyset$).
-- source:
--   Talluri, van Ryzin, Revenue management under a general discrete choice model of consumer behavior, working paper of October 21, 2001 (UPF Economics Working Paper 533; published Management Science 50(1), 2004, DOI 10.1287/mnsc.1030.0147), pp. 19–20, discussion after Theorem 2 ("This later property is sufficient to ensure that the expected revenue is at least as large")

import Mathlib
import Definitions.Def_RevenueManagement_singleResource
import Definitions.Def_ChoiceRM_FareOrder_FareOrder

namespace ChoiceRM.FareOrder

open RevenueManagement

/-- pp. 19–20, after Theorem 2: if the mixture `P̄(α)` of complete sets has prefix sums at least
those of `P(T)` and the same total, then for every `x_1 ≥ … ≥ x_n` the mixture earns at least
as much as `T` in (9). -/
theorem mixture_dominates {n : ℕ} (P : Finset (Fin n) → Fin n → ℝ)
    (hP : IsChoiceModel P) (hsupp : SupportedOn P) (T : Finset (Fin n))
    (α : Fin (n + 1) → ℝ) (hα0 : ∀ k, 0 ≤ α k) (hα1 : ∑ k, α k = 1)
    (hpre : ∀ i, i < n → ∑ j ∈ complete n i, P T j ≤ ∑ j ∈ complete n i, mixProb P α j)
    (htot : ∑ j, mixProb P α j = ∑ j, P T j)
    (x : Fin n → ℝ) (hx : Antitone x) :
    fareValue P x T ≤ ∑ k : Fin (n + 1), α k * fareValue P x (complete n k.val) := by sorry

end ChoiceRM.FareOrder
