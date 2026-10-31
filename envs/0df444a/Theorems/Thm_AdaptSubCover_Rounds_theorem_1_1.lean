-- Prove2me | Theorems.Thm_AdaptSubCover_Rounds_theorem_1_1
-- name    : AdaptSubCover.Rounds.theorem_1_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T07:17:55.064779+00:00
-- url     : https://prove2.me/theorems/7766309b-fd9a-4999-ae67-2aecc2cd618e
-- title:
--   Theorem 1.1, p. 3 — for independent items, some r-round adaptive policy costs O(Q^{1/r} log Q) times every feasible adaptive policy
-- statement:
--   **Theorem 1.1 (Independent Items).** There is an absolute constant $C > 0$ such that for every instance of stochastic submodular cover with independent items — a finite ground set $U$, a monotone submodular $f : 2^U \to \mathbb Z_{\ge 0}$ with $Q = f(U)$, and $m$ independent items with integer costs $c_i \ge 1$ — that some feasible adaptive solution covers, and every integer $r \ge 1$, there is an $r$-round-adaptive solution $\sigma$ that covers $f$ with probability one and satisfies
--
--   $$\mathbb E[\mathrm{cost}(\sigma)] \;\le\; C\cdot Q^{1/r}\,(1 + \ln Q)\cdot \mathbb E[\mathrm{cost}(\mathtt{OPT})]$$
--
--   for every feasible fully adaptive solution $\mathtt{OPT}$.
--
--   With $r = 1$ this bounds the adaptivity gap of stochastic submodular cover (and of stochastic set cover) by $O(Q \log Q)$; with $r = \log Q$ rounds it gives an $O(\log Q)$-approximation.
--
--   **Formalization Note.** The constant $C$ is chosen before the instance and $r$. "Times the cost of an optimal adaptive algorithm" is stated against every feasible adaptive solution, which is equivalent and avoids an infimum. $\log Q$ is read as $1 + \ln Q$: at $Q = 1$ the printed $\log Q$ is $0$ and would force cost $0$, which is false whenever $f(\emptyset) < Q$. Feasibility of the instance is assumed (otherwise the optimal cost is infinite). An $r$-round solution freezes each round's ordering at the start of the round and uses in-round realizations only to stop. The polynomial running time of the algorithm is not part of the statement.
-- source:
--   Ghuge, Gupta, Nagarajan, The Power of Adaptivity for Stochastic Submodular Cover, arXiv:2106.16115v1, p. 3, Theorem 1.1

import Mathlib
import Definitions.Def_AdaptSubCover_Rounds_Model

namespace AdaptSubCover.Rounds

theorem theorem_1_1 :
    ∃ C : ℝ, 0 < C ∧
      ∀ (U : Type) [Fintype U] [DecidableEq U] (m : ℕ) (I : Instance U m),
        I.Standing → (∃ π : AdaptivePolicy m U, I.Feasible π) → ∀ r : ℕ, 1 ≤ r →
          ∃ σ : RoundPolicy m U, I.FeasibleR r σ ∧
            ∀ π : AdaptivePolicy m U, I.Feasible π →
              I.expCostR r σ ≤
                C * (I.Q : ℝ) ^ ((1 : ℝ) / r) * (1 + Real.log I.Q) * I.expCost π := by sorry

end AdaptSubCover.Rounds
