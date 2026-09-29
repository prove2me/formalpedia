-- Prove2me | Theorems.Thm_BanditAlgorithm_mdp_regret_lower_bound_large_diameter
-- name    : BanditAlgorithm.mdp_regret_lower_bound_large_diameter
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-03T21:13:34.745798+00:00
-- url     : https://prove2.me/theorems/f396cfac-4ef3-426b-ae58-b06d1e0c2edc
-- title:
--   MDP minimax regret lower bound $\mathbb{E}[\hat R_n] \ge C\sqrt{DSAn}$ (strengthened diameter hypothesis)
-- statement:
--   (MDP minimax lower bound; L&S Theorem 38.7, with the diameter hypothesis strengthened) There is a universal constant $C > 0$ such that for all $S \ge 3$, $A \ge 2$, $D \ge 20\,(1 + \log_A S)$ and $n \ge DSA$: for any policy $\pi$ there exists an MDP $M$ with $S$ states, $A$ actions, rewards in $[0,1]$ and diameter at most $D$ (stated via the $[0,\infty]$-valued diameter, which forces $M$ to be strongly connected) and an initial state distribution such that
--
--   $$\mathbb{E}[\hat R_n] \ge C\sqrt{DSAn}.$$
--
--   **Why the hypothesis differs from the book.** L&S state this with $D \ge 6 + 2\log_A S$, which appears too weak. In the §38.7 construction the diameter is realised by the pair $(s_g,s_b)$ and equals $2(1/\delta + d + 1)$, so $D(M) \le D$ forces $1/\delta \le D/2 - (d+1)$; a tree with $\Omega(S)$ leaves needs depth $d \gtrsim \log_A S$, so at the boundary $d+1 \approx D/2$ and the sojourn collapses to $1/\delta = O(1)$. The $\sqrt{D}$ in $\sqrt{DSAn}$ *is* the sojourn — each decision carries $\Theta(D)$ rounds of reward consequence but returns one bit of feedback — so with $1/\delta = O(1)$ the construction yields only $\sqrt{SAn/D}$. The original paper (Jaksch, Ortner & Auer, JMLR 11 (2010) 1563-1600, Thm 5) assumes $D \ge 20\log_A S$ with $S,A \ge 10$. The form $20(1 + \log_A S)$ used here implies both $D \ge 20$ and $D \ge 20\log_A S$ and keeps $1/\delta \ge 0.4\,D$ uniformly, so no case split for small $D$ is needed. The constant $20$ is not optimised: any $c$ leaving $\Theta(D)$ slack works.
-- source:
--   L&S Theorem 38.7, p.523, with the diameter hypothesis strengthened to D >= 20(1+log_A S) following Jaksch-Ortner-Auer, JMLR 11 (2010) 1563-1600, Thm 5

import Definitions.Def_FiniteMDPLearning
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic


open MeasureTheory ProbabilityTheory

theorem BanditAlgorithm.mdp_regret_lower_bound_large_diameter :
    ∃ C : ℝ, 0 < C ∧
      ∀ S A n : ℕ, ∀ D : ℝ, 3 ≤ S → 2 ≤ A →
        20 * (1 + Real.log S / Real.log A) ≤ D → D * S * A ≤ n →
        ∀ π : MDPPolicy S A,
          ∃ M : FiniteMDP S A, ∃ μ0 : MDPStateDistribution S,
            mdpDiameterENN M ≤ ENNReal.ofReal D ∧
            C * Real.sqrt (D * S * A * n) ≤
              ∫ h, mdpRegret M n h ∂(mdpMeasure M μ0 π n) := by
  sorry
