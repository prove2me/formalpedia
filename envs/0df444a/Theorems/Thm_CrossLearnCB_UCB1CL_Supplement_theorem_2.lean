-- Prove2me | Theorems.Thm_CrossLearnCB_UCB1CL_Supplement_theorem_2
-- name    : CrossLearnCB.UCB1CL.Supplement.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T04:52:05.961388+00:00
-- url     : https://prove2.me/theorems/5883b145-49d2-4ae1-b894-99bd632ccbff
-- title:
--   Theorem 2, p. 21 — EXP3.CL has expected ex ante regret O(√(λ̄KT log K)) with adversarial rewards and stochastic contexts
-- statement:
--   Consider the contextual bandit problem with cross-learning with $K$ arms, $C$ contexts and horizon $T$: contexts are drawn i.i.d. from a distribution $D$ on $[C]$ known to the learner, the CL graphs $G_1, \dots, G_K$ contain all self-loops, and an oblivious adversary fixes a reward table $r_{i,t}(c) \in [0,1]$ before the game. Let $\lambda(G_i)$ be the maximum acyclic subgraph number of $G_i$ and $\bar\lambda = \frac1K \sum_i \lambda(G_i)$.
--
--   There is an absolute constant $C_0$ such that, for every such instance with $K\log K \le \bar\lambda T$, EXP3.CL (Algorithm 2) satisfies
--
--   $$\mathbb E[\mathrm{Reg}(\mathrm{EXP3.CL})] = \sum_{c} D(c)\max_{i} \sum_{t=1}^T r_{i,t}(c) - \mathbb E\Big[\sum_{t=1}^T r_{I_t,t}(c_t)\Big] \le C_0 \sqrt{\bar\lambda K T \log K},$$
--
--   the expectation over the contexts and the algorithm's randomness. The benchmark is the ex ante one, $\pi(c) \in \arg\max_i \sum_t r_{i,t}(c)$.
--
--   With complete cross-learning ($\lambda = 1$) the bound is $O(\sqrt{KT\log K})$, independent of $C$; with no cross-learning it is $O(\sqrt{CKT\log K})$, the rate of running EXP3 separately in every context.
--
--   **Formalization Note** The constant $C_0$ is quantified before $K$, $C$, $T$, the graphs, $D$ and the table, so it is absolute. The condition $K\log K \le \bar\lambda T$ is exactly $K\alpha \le 1$, under which Algorithm 2's $p_{i,t}$ are probabilities (the paper's footnote 6 uses $T \ge K\log K$, which implies it). The expectation is the finite sum over context–arm trajectories of the protocol definitions.
--
--   Differences from the source:
--   - encoding: regret O(√(λ̄KT log K)) → there is C₀ : ℝ, chosen before K, C, T, G, D and r, with E[Reg] ≤ C₀ √(λ̄KT log K); reason: the meaning of O(·) with an absolute constant
--   - reading: Algorithm 2 run on every instance → the bound is asserted when K log K ≤ λ̄T; reason: this is Kα ≤ 1, without which (1 − Kα)w/W + α is not a probability vector and the algorithm is undefined; footnote 6 (p. 47) assumes T ≥ K log K, which implies it since λ̄ ≥ 1
--   - encoding: E[Σ_t r_{π(c_t),t}(c_t) − Σ_t r_{I_t,t}(c_t)] with π(c) = argmax_i Σ_t r_{i,t}(c) → Σ_c D(c) max_i Σ_t r_{i,t}(c) − E[Σ_t r_{I_t,t}(c_t)], the expectation a finite sum over trajectories with weight ∏_t D(c_t) p_t(I_t); reason: the paper's identity on p. 10 (contexts are i.i.d. D); the maximum makes ties irrelevant
--   - encoding: rounds 1..T, an oblivious adversarial table → 0-based rounds Fin T and a fixed table r : Fin T → Fin K → Fin C → ℝ; reason: same instances; a table drawn at random before the game is covered by averaging
-- source:
--   Balseiro et al., Contextual Bandits with Cross-Learning, arXiv:1809.09582v3, p. 21, Theorem 2; Algorithm 2 p. 22; proof pp. 46–48, App. C.2 (footnote 6, p. 47)

import Mathlib
import Definitions.Def_CrossLearnCB_UCB1CL_Model
import Definitions.Def_CrossLearnCB_UCB1CL_Supplement_AcyclicNumber
import Definitions.Def_CrossLearnCB_UCB1CL_Supplement_Protocol
import Definitions.Def_CrossLearnCB_UCB1CL_Supplement_Algorithms

namespace CrossLearnCB.UCB1CL.Supplement

/-- Theorem 2, p. 21: there is an absolute constant `C₀` such that EXP3.CL (Algorithm 2), run
with the known context distribution `D`, has expected ex ante regret at most
`C₀ √(λ̄ K T log K)` against every oblivious reward table with values in `[0, 1]`, whenever its
probabilities are well defined (`K log K ≤ λ̄ T`, i.e. `Kα ≤ 1`). -/
theorem theorem_2 : ∃ C₀ : ℝ, ∀ (K C T : ℕ) [NeZero K] (G : Fin K → Fin C → Fin C → Prop),
    HasSelfLoops G → ∀ D : Fin C → ℝ, IsDistribution D →
    (K : ℝ) * Real.log K ≤ lambdaBar G * T →
    ∀ r : Fin T → Fin K → Fin C → ℝ, (∀ t i c, r t i c ∈ Set.Icc (0 : ℝ) 1) →
      exAnteRegret G D (exp3CL T G D) r
        ≤ C₀ * Real.sqrt (lambdaBar G * K * T * Real.log K) := by sorry

end CrossLearnCB.UCB1CL.Supplement
