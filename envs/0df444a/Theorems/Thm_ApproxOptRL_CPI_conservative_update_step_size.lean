-- Prove2me | Theorems.Thm_ApproxOptRL_CPI_conservative_update_step_size
-- name    : ApproxOptRL.CPI.conservative_update_step_size
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T10:45:45.500995+00:00
-- url     : https://prove2.me/theorems/b8e70880-d5be-4e3d-bc70-0dd187c2a700
-- title:
--   Corollary 4.2 — the step size $\alpha=\frac{(1-\gamma)\mathbb A}{4R}$ improves $\eta_\mu$ by at least $\frac{\mathbb A^2}{8R}$
-- statement:
--   Consider a finite MDP with nonempty state set $S$, nonempty action set $A$, transition probabilities $P(s';s,a)$, rewards $\mathcal R(s,a)\in[0,R]$ with $R>0$, and discount factor $0\le\gamma<1$; let $\mu$ be a state distribution and let $\pi$, $\pi'$ be policies.
--
--   Let $\mathbb A = \mathbb A_{\pi,\mu}(\pi')$ be the policy advantage of $\pi'$ with respect to $\pi$ and $\mu$. If $\mathbb A\ge 0$, then the conservative update $\pi_{new} = (1-\alpha)\pi+\alpha\pi'$ with
--   $$\alpha = \frac{(1-\gamma)\mathbb A}{4R}$$
--   guarantees the policy improvement
--   $$\eta_\mu(\pi_{new}) - \eta_\mu(\pi) \ge \frac{\mathbb A^2}{8R}.$$
--
--   The larger the policy advantage, the larger the guaranteed increase in performance; this is the quantitative improvement that bounds the number of iterations of conservative policy iteration.
--
--   **Formalization Note** The paper's "$R$ the maximal possible reward" is formalized as any upper bound $R>0$ on the rewards (rewards in $[0,R]$), not necessarily attained; the statement is the paper's for the attained maximum and holds for every such bound. The condition $\alpha\le1$ is not assumed: it follows from $\mathbb A\le R$.
-- source:
--   Kakade, Langford, Approximately Optimal Approximate Reinforcement Learning, ICML 2002, p. 5, Corollary 4.2

import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_IsTransitionKernel
import Definitions.Def_FoundationsML_ReinforcementLearning_IsPolicy
import Definitions.Def_ApproxOptRL_Shared_Model
import Definitions.Def_ApproxOptRL_CPI_PolicyAdvantage
open ApproxOptRL.Shared
open FoundationsML.ReinforcementLearning

namespace ApproxOptRL.CPI

/-- **Corollary 4.2** (Kakade–Langford, ICML 2002, p. 5). Let `R` be the maximal possible
reward and `𝔸 = 𝔸_{π,μ}(π')` the policy advantage of `π'` with respect to `π` and `μ`. If
`𝔸 ≥ 0`, then the update (4.1) with `α = (1 - γ)𝔸/(4R)` guarantees
`η_μ(π_new) - η_μ(π) ≥ 𝔸²/(8R)`.
`R` is any upper bound on the rewards (rewards in `[0, R]`, `R > 0`), not necessarily the
attained maximum. Standing assumptions of §2: finite nonempty `S`, `A`; transition kernel `P`;
`0 ≤ γ < 1`; `μ` a state distribution. -/
theorem conservative_update_step_size {S A : Type} [Fintype S] [Fintype A] [DecidableEq S]
    [Nonempty S] [Nonempty A]
    (P : S → A → S → ℝ) (hP : IsTransitionKernel P)
    (r : S → A → ℝ) (R : ℝ) (hR : 0 < R) (hr : ∀ s a, 0 ≤ r s a ∧ r s a ≤ R)
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (μ : S → ℝ) (hμ : IsStateDist μ)
    (π π' : S → A → ℝ) (hπ : IsPolicy π) (hπ' : IsPolicy π')
    (hA : 0 ≤ policyAdvantage P r γ π μ π') :
    let α : ℝ := (1 - γ) * policyAdvantage P r γ π μ π' / (4 * R)
    (policyAdvantage P r γ π μ π') ^ 2 / (8 * R) ≤
      eta P r γ (mixPolicy α π π') μ - eta P r γ π μ := by sorry

end ApproxOptRL.CPI
