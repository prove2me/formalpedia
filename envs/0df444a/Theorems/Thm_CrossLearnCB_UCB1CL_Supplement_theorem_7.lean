-- Prove2me | Theorems.Thm_CrossLearnCB_UCB1CL_Supplement_theorem_7
-- name    : CrossLearnCB.UCB1CL.Supplement.theorem_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T04:58:20.45736+00:00
-- url     : https://prove2.me/theorems/5deedfe9-be09-4287-bd19-628eb15b0d47
-- title:
--   Theorem 7, p. 39 — ex post regret: liminf_{C→∞} E[Reg_Post(A)] ≥ T/2 for every algorithm (adversarial rewards, stochastic contexts)
-- statement:
--   Fix a horizon $T$. Consider the instance with $K = 2$ arms and $C$ contexts drawn uniformly at random, in which, independently for every round $t$ and context $c$, a fair coin decides whether $r_{1,t}(c) = 1, r_{2,t}(c) = 0$ or $r_{1,t}(c) = 0, r_{2,t}(c) = 1$; the rewards are drawn before the game, independently of the contexts and of the algorithm. Measure regret against the **ex post** benchmark, best in hindsight for the realized contexts:
--
--   $$\mathrm{Reg}_{\mathrm{Post}}(A) = \sum_{c} \max_{i} \sum_{t:\,c_t = c} r_{i,t}(c) - \sum_{t=1}^T r_{I_t,t}(c_t).$$
--
--   Then for every $\varepsilon > 0$ there is $C_0$ such that, for every $C \ge C_0$, every choice of CL graphs (with self-loops) and every algorithm $A$,
--
--   $$\mathbb E[\mathrm{Reg}_{\mathrm{Post}}(A)] \ge \frac T2 - \varepsilon ,$$
--
--   the expectation over the rewards, the contexts and the algorithm's randomness. In particular, for every algorithm (for every $C$), $\liminf_{C\to\infty}\mathbb E[\mathrm{Reg}_{\mathrm{Post}}(A)] \ge T/2$.
--
--   Hence no algorithm has ex post regret sublinear in $T$ uniformly in the number of contexts, which is why Theorems 2–3 use the ex ante benchmark.
--
--   **Formalization Note** Arms `0` and `1` are the paper's arms 1 and 2. The expectation over the rewards is the average over all coin patterns $b : [T]\times[C] \to \{0,1\}$; for each pattern the expectation over contexts and the algorithm is the finite trajectory sum of the protocol definitions. An algorithm is any valid policy with cross-learning feedback.
--
--   Differences from the source:
--   - generalization: for any algorithm A there is an instance (with cross-learning) → one explicit instance (K = 2, uniform contexts, fair-coin rewards, the instance of the proof on p. 40) works for every algorithm and every family of CL graphs with self-loops, with the threshold C₀ uniform in both; reason: specializing to a given A (and any graphs) gives the printed statement
--   - encoding: liminf_{C→∞} E[Reg_Post(A)] ≥ T/2 → for every ε > 0 there is C₀ with E[Reg_Post(A)] ≥ T/2 − ε for all C ≥ C₀; reason: this is the definition of liminf ≥ T/2 for a sequence (the regret is bounded by T, so the liminf is finite)
--   - encoding: randomized adversarial rewards and arms 1, 2 → the average over coin patterns of a fixed-table expectation, arms Fin 2; reason: the rewards are independent of the contexts and of the algorithm, so this is the joint expectation
-- source:
--   Balseiro et al., Contextual Bandits with Cross-Learning, arXiv:1809.09582v3, p. 39, Theorem 7; proof pp. 40–41 (instance p. 40, (8) p. 40, (9) p. 41)

import Mathlib
import Definitions.Def_CrossLearnCB_UCB1CL_Model
import Definitions.Def_CrossLearnCB_UCB1CL_Supplement_Protocol

namespace CrossLearnCB.UCB1CL.Supplement

/-- Theorem 7, p. 39: with `K = 2` arms, uniform contexts, and each round–context pair an
independent fair coin deciding which arm pays `1` (the other pays `0`), the expected ex post
regret of every algorithm, under any CL graphs, is at least `T/2 − ε` once the number of
contexts `C` is large enough; i.e. `liminf_{C→∞} E[Reg_Post(A)] ≥ T/2`, uniformly in `A`. -/
theorem theorem_7 (T : ℕ) : ∀ ε : ℝ, 0 < ε → ∃ C₀ : ℕ, ∀ C : ℕ, C₀ ≤ C →
    ∀ G : Fin 2 → Fin C → Fin C → Prop, HasSelfLoops G →
    ∀ A : Policy 2 C, A.IsValid →
      (T : ℝ) / 2 - ε ≤ coinExPostRegret T C G A := by sorry

end CrossLearnCB.UCB1CL.Supplement
