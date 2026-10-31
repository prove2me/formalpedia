-- Prove2me | Theorems.Thm_AdaptSubCover_Rounds_theorem_3_2
-- name    : AdaptSubCover.Rounds.theorem_3_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T07:18:53.152984+00:00
-- url     : https://prove2.me/theorems/39fb96e0-ce4d-4cd0-b5ce-cef195e4f104
-- title:
--   Theorem 3.2, p. 8 — Algorithm 2 (SSC) is an r-round adaptive algorithm with cost O(Q^{1/r} log Q) times the optimal adaptive cost
-- statement:
--   There is an absolute constant $C > 0$ such that for every instance of stochastic submodular cover with independent items that some feasible adaptive solution covers, and every integer $r \ge 1$:
--
--   1. some $r$-round solution follows Algorithm 2, $\mathrm{SSC}(r, \mathcal X, f)$;
--   2. every $r$-round solution $\sigma$ that follows $\mathrm{SSC}(r, \mathcal X, f)$ covers $f$ with probability one after its $r$ rounds, and for every feasible adaptive solution $\mathtt{OPT}$,
--   $$\mathbb E[\mathrm{cost}(\sigma)] \;\le\; C\cdot Q^{1/r}\,(1 + \ln Q)\cdot \mathbb E[\mathtt{OPT}].$$
--
--   **Formalization Note.** $O(\log Q)$ is read as $C(1 + \ln Q)$, since $\log Q = 0$ at $Q = 1$ while the cost need not vanish. SSC uses in each round the power-of-two parameter $\delta'$ with $\delta/2 < \delta' \le \delta$, $\delta = \hat Q^{-1/(\text{rounds left})}$ (p. 10). Every tie-break of the greedy list is covered. The running-time remark of p. 9 is not formalized.
-- source:
--   Ghuge, Gupta, Nagarajan, The Power of Adaptivity for Stochastic Submodular Cover, arXiv:2106.16115v1, p. 8, Theorem 3.2, Algorithm 2

import Mathlib
import Definitions.Def_AdaptSubCover_Rounds_ParCA

namespace AdaptSubCover.Rounds

theorem theorem_3_2 :
    ∃ C : ℝ, 0 < C ∧
      ∀ (U : Type) [Fintype U] [DecidableEq U] (m : ℕ) (I : Instance U m),
        I.Standing → (∃ π : AdaptivePolicy m U, I.Feasible π) → ∀ r : ℕ, 1 ≤ r →
          (∃ σ : RoundPolicy m U, I.IsSSC r σ) ∧
          ∀ σ : RoundPolicy m U, I.IsSSC r σ →
            I.FeasibleR r σ ∧
            ∀ π : AdaptivePolicy m U, I.Feasible π →
              I.expCostR r σ ≤
                C * (I.Q : ℝ) ^ ((1 : ℝ) / r) * (1 + Real.log I.Q) * I.expCost π := by sorry

end AdaptSubCover.Rounds
