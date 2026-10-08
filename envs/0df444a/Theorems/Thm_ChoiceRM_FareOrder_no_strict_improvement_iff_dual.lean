-- Prove2me | Theorems.Thm_ChoiceRM_FareOrder_no_strict_improvement_iff_dual
-- name    : ChoiceRM.FareOrder.no_strict_improvement_iff_dual
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:48:51.258896+00:00
-- url     : https://prove2.me/theorems/92b7412c-ae2c-433e-b91f-93163ca74a85
-- title:
--   Proof of Theorem 2, p. 20 — Farkas: (10)–(11) has no solution iff the dual system in (α, z) is solvable
-- statement:
--   Throughout, $N = \{1, \dots, n\}$ is the set of fare products, indexed in fare order $r_1 \ge r_2 \ge \dots \ge r_n \ge 0$. A **choice model** assigns to every offer set $S \subseteq N$ and product $j$ a purchase probability $P_j(S) \ge 0$, with $P_j(S) = 0$ for $j \notin S$ and $Q(S) = \sum_{j \in S} P_j(S) \le 1$ (the no-purchase probability is $P_0(S) = 1 - Q(S)$). The **complete sets** are $A_k = \{1, \dots, k\}$ for $k = 0, 1, \dots, n$, with $A_0 = \emptyset$; every other set is **incomplete**.
--
--   Let $T \subseteq N$ be any offer set. The system (10)–(11) — values $x_1 \ge \dots \ge x_n$ and a scalar $u$ with $u < \sum_{j \in T} x_j P_j(T)$ and $\sum_{j \in A_k} x_j P_j(A_k) \le u$ for $k = 0, \dots, n$ — has no solution if and only if there exist $\alpha_0, \dots, \alpha_n \ge 0$ and $z_0, \dots, z_n \ge 0$ with $z_0 = z_n = 0$ such that
--
--   $$\sum_{k=0}^n \alpha_k P_j(A_k) - z_j + z_{j-1} = P_j(T) \quad (j = 1, \dots, n), \qquad \sum_{k=0}^n \alpha_k = 1.$$
--
--   This is the Farkas-lemma step of the proof of Theorem 2: $\alpha_k$ is the multiplier of the constraint for $A_k$ and $z_j$ that of $x_j \ge x_{j+1}$.
--
--   **Formalization Note** Fare $j \in \{1, \dots, n\}$ is the element $j - 1$ of `Fin n`; the order $x_1 \ge \dots \ge x_n$ is `Antitone x`; $A_k$ is `complete n k`; the choice-model axioms are `IsChoiceModel P` (platform definition `RevenueManagement_singleResource`) together with `SupportedOn P` ($P_j(S) = 0$ off $S$, the model's own convention on p. 5). $z$ is indexed by `Fin (n + 1)`, with $z_j \mapsto$ `z j.succ` and $z_{j-1} \mapsto$ `z j.castSucc` for the 0-based product index `j`. Complete sets are indexed by $k \in \{0, \dots, n\}$, so $A_0 = \emptyset$ counts as complete and the weights $\alpha$ live on $n + 1$ sets. The page indexes the weights by $k = 1, \dots, n$; the paper notes on p. 21 that Theorem 2 holds for any specified family of sets, and with $A_0$ included the property is the one the paper's Propositions 5 and 6 need (for MNL and all $x_j < 0$, the unique optimum of (9) is $\emptyset$).
-- source:
--   Talluri, van Ryzin, Revenue management under a general discrete choice model of consumer behavior, working paper of October 21, 2001 (UPF Economics Working Paper 533; published Management Science 50(1), 2004, DOI 10.1287/mnsc.1030.0147), p. 20, proof of Theorem 2, the dual system following (10)–(11)

import Mathlib
import Definitions.Def_RevenueManagement_singleResource
import Definitions.Def_ChoiceRM_FareOrder_FareOrder
import Definitions.Def_ChoiceRM_FareOrder_Systems

namespace ChoiceRM.FareOrder

open RevenueManagement

/-- Proof of Theorem 2, p. 20 (Farkas' lemma): for an offer set `T`, the system (10)–(11) has no
solution iff the dual system in `(α, z)` is solvable. -/
theorem no_strict_improvement_iff_dual {n : ℕ} (P : Finset (Fin n) → Fin n → ℝ)
    (hP : IsChoiceModel P) (hsupp : SupportedOn P) (T : Finset (Fin n)) :
    NoStrictImprovement P T ↔ DualSolvable P T := by sorry

end ChoiceRM.FareOrder
