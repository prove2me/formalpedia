-- Prove2me | Theorems.Thm_BudgetClock_PostedSym_theorem_15
-- name    : BudgetClock.PostedSym.theorem_15
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T06:24:27.465982+00:00
-- url     : https://prove2.me/theorems/f2fb3ba8-0c7b-47b4-bfe9-6b0afebae27a
-- title:
--   Theorem 15, p. 27 — Mechanism 5 is budget feasible and an O(log n)-approximation for symmetric submodular valuations
-- statement:
--   Consider $n$ bidders with private costs $0 \le c_i \le B$, a budget $B > 0$, and a symmetric submodular valuation $v$ of the auctioneer: $v(S) = \sum_{i=1}^{|S|} r_i$ for some $r_1 \ge \cdots \ge r_n \ge 0$. Let $W$ be the winning set of the posted-price Mechanism 5, run with an arbitrary set-aside bidder $j$, and let $p_i$ be the price it offers to bidder $i$.
--
--   **Theorem 15.** There is an absolute constant $C > 0$ such that for every $n \ge 2$, every symmetric submodular $v$, every $B > 0$, every cost vector with $0 \le c_i \le B$ and every choice of $j$,
--   $$\sum_{i \in W} p_i \le B \qquad\text{and}\qquad v(O) \le C \ln n \cdot v(W)\ \text{ for every } O \subseteq N \text{ with } \sum_{i\in O} c_i \le B.$$
--
--   In the paper's words, Mechanism 5 obtains an $O(\log n)$ approximation to the optimal value for instances with symmetric submodular valuations. It complements the paper's lower bound for the same class (Theorem 14), which shows that no deterministic posted-price mechanism achieves an approximation better than $\log n / 4$ for this class, so the order $\log n$ is tight.
--
--   **Formalization Note.** $O(\log n)$ is stated with a constant $C$ chosen before all instances, so it is uniform in $n$, $v$, $B$, $c$ and $j$. The optimum is expressed without a supremum: $v(O) \le C\ln n\cdot v(W)$ for every budget-feasible $O$ at true costs. The threshold $n \ge 2$ is needed because $\ln 1 = 0$: at $n = 1$ the offered price $B/(2\ln n)$ would be a division by zero. $B > 0$ is an added hypothesis (the paper says only "a budget $B$"). $c_i \le B$ is the paper's standing assumption for Mechanism 5 (p. 27). Budget feasibility of the payments is not in the theorem's sentence but is the opening claim of its proof and a requirement of every mechanism in the paper; it is the first conjunct. Mechanism 5 is formalized with the set-aside bidder $j$ joining $W$ when it accepts the offer $B$, which the printed pseudocode omits but the proof assumes; without it the theorem is false. Running time, determinism and the posted-price property hold by construction and are not stated.
-- source:
--   Balkanski et al., Deterministic Budget-Feasible Clock Auctions, arXiv:2107.09239v2, p. 27, Theorem 15

import Mathlib
import Definitions.Def_BudgetClock_PostedSym_Setting

namespace BudgetClock.PostedSym

theorem theorem_15 :
    ∃ C : ℝ, 0 < C ∧
      ∀ (n : ℕ), 2 ≤ n →
      ∀ (v : Finset (Fin n) → ℝ), IsSymmetricSubmodular n v →
      ∀ (B : ℝ), 0 < B →
      ∀ (c : Fin n → ℝ), (∀ i, 0 ≤ c i) → (∀ i, c i ≤ B) →
      ∀ (j : Fin n),
        (∑ i ∈ (mech5 n B c j).1, (mech5 n B c j).2 i ≤ B) ∧
        ∀ O : Finset (Fin n), ∑ i ∈ O, c i ≤ B →
          v O ≤ C * Real.log n * v (mech5 n B c j).1 := by sorry

end BudgetClock.PostedSym
