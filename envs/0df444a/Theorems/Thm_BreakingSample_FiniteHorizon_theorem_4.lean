-- Prove2me | Theorems.Thm_BreakingSample_FiniteHorizon_theorem_4
-- name    : BreakingSample.FiniteHorizon.theorem_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:47:59.179724+00:00
-- url     : https://prove2.me/theorems/d8973749-4a4c-4c9e-bf23-83d2ec0a376d
-- title:
--   Theorem 4, p. 10 — finite-horizon model-based planning is ε-optimal w.p. ≥ 1 − δ once N ≥ c₀H³log(H|S||A|/δ)/ε²
-- statement:
--   Let $\mathcal M=(\mathcal S,\mathcal A,\{P_h\}_{h=1}^H,\{r_h\}_{h=1}^H,H)$ be a time-inhomogeneous finite-horizon MDP with finite state space $\mathcal S$, finite nonempty action space $\mathcal A$, transition kernels $P_h$ and rewards $r_h(s,a)\in[0,1]$. For every triple $(s,a,h)$ a generative model supplies $N$ independent samples $s^i_h(s,a)\sim P_h(\cdot\mid s,a)$; the empirical MDP $\widehat{\mathcal M}$ replaces each $P_h$ by its empirical frequency $\widehat P_h$. Model-based planning returns the policy $\widehat\pi^\star$ obtained by backward dynamic programming on $\widehat{\mathcal M}$.
--
--   **Theorem 4.** There is a universal constant $c_0>0$ such that for every such MDP, every $\delta>0$ and every $0<\varepsilon\le H$: if
--   $$N\ge\frac{c_0H^3\log\big(H|\mathcal S||\mathcal A|/\delta\big)}{\varepsilon^2},$$
--   then with probability at least $1-\delta$,
--   $$\forall(s,a,h)\in\mathcal S\times\mathcal A\times[H]:\qquad V^{\widehat\pi^\star}_h(s)\ge V^\star_h(s)-\varepsilon\quad\text{and}\quad Q^{\widehat\pi^\star}_h(s,a)\ge Q^\star_h(s,a)-\varepsilon.$$
--
--   The total number of samples is $NH|\mathcal S||\mathcal A|$, so the guarantee holds with $\widetilde O(|\mathcal S||\mathcal A|H^4/\varepsilon^2)$ samples over the full range $\varepsilon\in(0,H]$, and it applies as soon as $N\gtrsim H$ up to logarithmic factors.
--
--   **Formalization Note** The page names "universal constants $c_0,c_1>0$", but $c_1$ does not occur in the theorem; only $c_0$ is quantified. The constant is quantified before the spaces, the horizon and the MDP, so it cannot depend on them. The dynamic program breaks ties between empirical $Q$-values by a rule fixed before the data (any argmax rule); the conclusion holds for every such rule. Values are defined by the backward Bellman recursion and $V^\star_h$ as the maximum over deterministic nonstationary policies. "With probability at least $1-\delta$" is written as a bound $\le\delta$ on the probability of the failure event. $N>0$ is the standing assumption of (6). Steps are 0-based in Lean.
-- source:
--   arXiv:2005.12900v8, §4.2, Theorem 4, (19)–(20), p. 10

import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_IsTransitionKernel
import Definitions.Def_BreakingSample_FiniteHorizon_Model
import Definitions.Def_BreakingSample_FiniteHorizon_Sampling

namespace BreakingSample.FiniteHorizon

/-- Theorem 4 (Model-based planning; arXiv:2005.12900v8, §4.2, (19)–(20), p. 10). There is a universal
constant `c₀ > 0` such that for every finite-horizon MDP with rewards in `[0,1]`, every `δ > 0`, every
`0 < ε ≤ H` and every tie-breaking rule `sel` of the dynamic program (fixed before the data), if
`N ≥ c₀H³ log(H|S||A|/δ)/ε²` samples are drawn for each triple `(s,a,h)`, then with probability at least
`1 − δ` the DP policy `π̂⋆` of the empirical MDP obeys `V^{π̂⋆}_h(s) ≥ V⋆_h(s) − ε` and
`Q^{π̂⋆}_h(s,a) ≥ Q⋆_h(s,a) − ε` for all `(s,a,h)`. -/
theorem theorem_4 :
    ∃ c₀ : ℝ, 0 < c₀ ∧
    ∀ (S A : Type) [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A] [Nonempty A] (H : ℕ)
      (P : Fin H → S → A → S → ℝ) (r : Fin H → S → A → ℝ), IsFHMDP P r →
    ∀ (δ ε : ℝ) (N : ℕ), 0 < δ → 0 < ε → ε ≤ H → 0 < N →
      c₀ * (H : ℝ) ^ 3 * Real.log ((H : ℝ) * Fintype.card S * Fintype.card A / δ) / ε ^ 2 ≤ (N : ℝ) →
    ∀ sel : Fin H → S → (A → ℝ) → A, IsArgmaxRule sel →
      sampleProb P N (fun x => ¬ ∀ (h : Fin H) (s : S) (a : A),
          optValue P r h.val s - ε ≤ value P r (dpPolicy (empKernel x) r sel) h.val s ∧
          optQ P r h s a - ε ≤ qValue P r (dpPolicy (empKernel x) r sel) h s a) ≤ δ := by sorry

end BreakingSample.FiniteHorizon
