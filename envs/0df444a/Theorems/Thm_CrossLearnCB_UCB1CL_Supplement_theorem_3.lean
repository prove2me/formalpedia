-- Prove2me | Theorems.Thm_CrossLearnCB_UCB1CL_Supplement_theorem_3
-- name    : CrossLearnCB.UCB1CL.Supplement.theorem_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T04:52:54.022421+00:00
-- url     : https://prove2.me/theorems/2e3f7560-1dd3-4e0d-8875-5393db267c53
-- title:
--   Theorem 3, p. 24 — EXP3.CL-U has expected ex ante regret O(λK^{1/3}T^{2/3}(log K)^{1/3}) without knowing the context distribution
-- statement:
--   Consider the contextual bandit problem with cross-learning with $K$ arms, $C$ contexts and horizon $T$, in which every arm has the same CL graph $G$ (containing all self-loops), contexts are drawn i.i.d. from a distribution $D$ on $[C]$ that the learner does **not** know, and an oblivious adversary fixes a reward table $r_{i,t}(c) \in [0,1]$ before the game. Let $\lambda = \lambda(G)$ be the maximum acyclic subgraph number of $G$.
--
--   There is an absolute constant $C_0$ such that, whenever $K\log K \le T$, EXP3.CL-U (Algorithm 3) satisfies
--
--   $$\mathbb E[\mathrm{Reg}(\mathrm{EXP3.CL\text{-}U})] = \sum_{c} D(c)\max_{i} \sum_{t=1}^T r_{i,t}(c) - \mathbb E\Big[\sum_{t=1}^T r_{I_t,t}(c_t)\Big] \le C_0\, \lambda\, K^{1/3}\, T^{2/3} (\log K)^{1/3},$$
--
--   the expectation over the contexts and the algorithm's randomness, against the ex ante benchmark $\pi(c) \in \arg\max_i \sum_t r_{i,t}(c)$.
--
--   Not knowing $D$ costs a $T^{2/3}$ rate instead of the $\sqrt T$ of EXP3.CL; with complete cross-learning ($\lambda = 1$) the bound does not depend on $C$.
--
--   **Formalization Note** $C_0$ is quantified before $K$, $C$, $T$, $G$, $D$ and the table. The algorithm's definition takes no context distribution, so it cannot use $D$; $D$ enters only the law of the contexts and the benchmark. The condition $K\log K \le T$ is exactly $K\alpha \le 1$ for $\alpha = (\log K/(K^2T))^{1/3}$, under which Algorithm 3's $p_{i,t}$ are probabilities. Powers $x^{1/3}$, $x^{2/3}$ are real powers of nonnegative numbers.
--
--   Differences from the source:
--   - encoding: regret O(λK^{1/3}T^{2/3}(log K)^{1/3}) → there is C₀ : ℝ, chosen before K, C, T, G, D and r, with E[Reg] ≤ C₀ λ(G) K^{1/3} T^{2/3} (log K)^{1/3}; reason: the meaning of O(·) with an absolute constant
--   - reading: Algorithm 3 run on every instance → the bound is asserted when K log K ≤ T; reason: this is Kα ≤ 1, without which (1 − Kα)w/W + α is not a probability vector and the algorithm is undefined (footnote 6, p. 47, uses the same condition)
--   - encoding: all CL graphs G_i equal to G → the graph family fun _ => G, with G c c for every c; reason: same instances
--   - encoding: E[Σ_t r_{π(c_t),t}(c_t) − Σ_t r_{I_t,t}(c_t)] with π(c) = argmax_i Σ_t r_{i,t}(c) → Σ_c D(c) max_i Σ_t r_{i,t}(c) − E[Σ_t r_{I_t,t}(c_t)], the expectation a finite sum over trajectories; reason: the paper's identity on p. 10; the maximum makes ties irrelevant
--   - encoding: rounds 1..T, an oblivious adversarial table → 0-based rounds Fin T and a fixed table r; reason: same instances; a random table drawn before the game is covered by averaging
-- source:
--   Balseiro et al., Contextual Bandits with Cross-Learning, arXiv:1809.09582v3, p. 24, Theorem 3; Algorithm 3 p. 23; proof pp. 50–51, App. C.5

import Mathlib
import Definitions.Def_CrossLearnCB_UCB1CL_Supplement_AcyclicNumber
import Definitions.Def_CrossLearnCB_UCB1CL_Supplement_Protocol
import Definitions.Def_CrossLearnCB_UCB1CL_Supplement_Algorithms

namespace CrossLearnCB.UCB1CL.Supplement

/-- Theorem 3, p. 24: there is an absolute constant `C₀` such that, when every arm has the same
CL graph `G`, EXP3.CL-U (Algorithm 3), which does not know the context distribution `D`, has
expected ex ante regret at most `C₀ λ(G) K^{1/3} T^{2/3} (log K)^{1/3}` against every oblivious
reward table with values in `[0, 1]`, whenever its probabilities are well defined
(`K log K ≤ T`, i.e. `Kα ≤ 1`). -/
theorem theorem_3 : ∃ C₀ : ℝ, ∀ (K C T : ℕ) [NeZero K] (G : Fin C → Fin C → Prop),
    (∀ c, G c c) → ∀ D : Fin C → ℝ, IsDistribution D →
    (K : ℝ) * Real.log K ≤ T →
    ∀ r : Fin T → Fin K → Fin C → ℝ, (∀ t i c, r t i c ∈ Set.Icc (0 : ℝ) 1) →
      exAnteRegret (fun _ : Fin K => G) D (exp3CLU T G) r
        ≤ C₀ * (maxAcyclicNumber G : ℝ) * (K : ℝ) ^ (1 / 3 : ℝ) * (T : ℝ) ^ (2 / 3 : ℝ)
          * Real.log K ^ (1 / 3 : ℝ) := by sorry

end CrossLearnCB.UCB1CL.Supplement
