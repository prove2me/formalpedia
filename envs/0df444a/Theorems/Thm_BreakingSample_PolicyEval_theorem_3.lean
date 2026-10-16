-- Prove2me | Theorems.Thm_BreakingSample_PolicyEval_theorem_3
-- name    : BreakingSample.PolicyEval.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T11:02:05.429703+00:00
-- url     : https://prove2.me/theorems/90c865d5-16b7-403f-add6-0e1384325711
-- title:
--   Theorem 3, p. 9 — the plug-in value V̂^π of a fixed policy is ε-accurate w.p. ≥ 1 − δ once N ≥ c₀ log(|S| log(e/(1−γ))/δ)/((1−γ)³ε²)
-- statement:
--   **Model-based policy evaluation.** Consider a discounted Markov decision process with finite state set $\mathcal S$, finite action set $\mathcal A$, transition kernel $P$, rewards $r(s,a)\in[0,1]$ and discount factor $0<\gamma<1$. A generative model returns, for every pair $(s,a)$, $N$ independent next states drawn from $P(\cdot\mid s,a)$; the empirical kernel $\widehat P(s'\mid s,a)$ is the fraction of those samples equal to $s'$. For a deterministic policy $\pi$ fixed independently of the data, the **plug-in estimate** $\widehat V^\pi$ is the value function of $\pi$ in the empirical MDP $(\mathcal S,\mathcal A,\widehat P,r,\gamma)$.
--
--   There is a universal constant $c_0>0$ such that for every such MDP, every policy $\pi$, every $0<\delta<1$ and every $0<\varepsilon\le\frac1{1-\gamma}$: if
--   $$
--   N\ge c_0\,\frac{\log\Big(\frac{|\mathcal S|\log\frac{e}{1-\gamma}}{\delta}\Big)}{(1-\gamma)^3\varepsilon^2},
--   $$
--   then with probability at least $1-\delta$,
--   $$
--   \big|\widehat V^\pi(s)-V^\pi(s)\big|\le\varepsilon\qquad\text{for all }s\in\mathcal S .
--   $$
--
--   The sample size covers the whole accuracy range $\varepsilon\in(0,\frac1{1-\gamma}]$; in particular the estimate is nontrivial as soon as $N$ exceeds $\frac1{1-\gamma}$ up to logarithmic factors.
--
--   **Formalization Note** "Universal" is encoded by quantifying $c_0$ before the state and action types, the kernel, the reward, the discount factor and the policy, so $c_0$ depends on none of them. The probability is the finite sum, over all data sets, of their product weights, and the claim is that the event "some state has error above $\varepsilon$" has probability at most $\delta$. The hypothesis $N>0$ (the standing assumption of (3), which divides by $N$) is implied by the sample-size condition whenever $\mathcal S$ is nonempty. $e=\exp(1)$ and $\log$ is the natural logarithm.
-- source:
--   arXiv:2005.12900v8, Theorem 3, (15)–(16), §3.2, p. 9

import Mathlib
import Definitions.Def_BreakingSample_Perturbed_Model
import Definitions.Def_BreakingSample_Perturbed_Sampling

namespace BreakingSample.PolicyEval

/-- Theorem 3 (Model-based policy evaluation), (15)–(16), arXiv:2005.12900v8, §3.2, p. 9. There is a
universal constant `c₀ > 0` such that for every finite discounted MDP with rewards in `[0,1]`, every
policy `π` fixed independently of the data, every `0 < δ < 1` and `0 < ε ≤ 1/(1−γ)`: if
`N ≥ c₀ log(|S| log(e/(1−γ))/δ)/((1−γ)³ε²)`, then with probability at least `1 − δ` the plug-in
estimate `V̂^π` (the value of `π` in the empirical MDP) satisfies `|V̂^π(s) − V^π(s)| ≤ ε` for all `s`. -/
theorem theorem_3 :
    ∃ c₀ : ℝ, 0 < c₀ ∧
    ∀ (S A : Type) [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]
      (P : S → A → S → ℝ) (r : S → A → ℝ) (γ : ℝ), BreakingSample.Perturbed.IsDiscountedMDP P r γ →
    ∀ (π : S → A) (δ ε : ℝ) (N : ℕ), 0 < δ → δ < 1 → 0 < ε → ε ≤ 1 / (1 - γ) → 0 < N →
      c₀ * Real.log ((Fintype.card S : ℝ) * Real.log (Real.exp 1 / (1 - γ)) / δ)
          / ((1 - γ) ^ 3 * ε ^ 2) ≤ (N : ℝ) →
      BreakingSample.Perturbed.sampleProb P N (fun x => ¬ ∀ s,
        |BreakingSample.Perturbed.value (BreakingSample.Perturbed.empKernel x) r γ π s - BreakingSample.Perturbed.value P r γ π s| ≤ ε) ≤ δ := by sorry

end BreakingSample.PolicyEval
