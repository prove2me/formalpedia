-- Prove2me | Theorems.Thm_ApproxOptRL_CPI_performance_difference
-- name    : ApproxOptRL.CPI.performance_difference
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T10:44:39.780341+00:00
-- url     : https://prove2.me/theorems/77062d5a-f64f-40da-bbbc-7b3365efa254
-- title:
--   Lemma 6.1 — performance difference: $\eta_\mu(\tilde\pi)-\eta_\mu(\pi)=\frac1{1-\gamma}E_{(a,s)\sim\tilde\pi d_{\tilde\pi,\mu}}[A_\pi(s,a)]$
-- statement:
--   Consider a finite MDP with nonempty state set $S$, nonempty action set $A$, transition probabilities $P(s';s,a)$, rewards $\mathcal R(s,a)\in[0,R]$ with $R>0$, and discount factor $0\le\gamma<1$. Let $V_\pi$, $A_\pi$, $d_{\pi,\mu}$ and $\eta_\mu(\pi)=E_{s\sim\mu}[V_\pi(s)]$ be the normalized value function, the advantage, the discounted future state distribution and the performance measure.
--
--   For any policies $\tilde\pi$ and $\pi$ and any starting state distribution $\mu$,
--   $$\eta_\mu(\tilde\pi) - \eta_\mu(\pi) = \frac{1}{1-\gamma}\,E_{(a,s)\sim\tilde\pi d_{\tilde\pi,\mu}}\big[A_\pi(s,a)\big] = \frac{1}{1-\gamma}\sum_s d_{\tilde\pi,\mu}(s)\sum_a\tilde\pi(a;s)\,A_\pi(s,a).$$
--
--   The states are weighted by $d_{\tilde\pi,\mu}$, the discounted future state distribution of the **new** policy $\tilde\pi$, while the advantage is that of the **old** policy $\pi$. The identity expresses the change of performance exactly through the advantages of the old policy, and it is the basic tool behind the improvement bound for the conservative update (Theorem 4.1) and the quality bound for policies with small policy advantage.
--
--   **Formalization Note** The Lean variable `πt` stands for $\tilde\pi$. The hypotheses (transition kernel, rewards in $[0,R]$, $0\le\gamma<1$, policies, state distribution) are the paper's standing assumptions of §2.
-- source:
--   Kakade, Langford, Approximately Optimal Approximate Reinforcement Learning, ICML 2002, p. 6, Lemma 6.1

import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_IsTransitionKernel
import Definitions.Def_FoundationsML_ReinforcementLearning_IsPolicy
import Definitions.Def_ApproxOptRL_Shared_Model
open ApproxOptRL.Shared
open FoundationsML.ReinforcementLearning

namespace ApproxOptRL.CPI

/-- **Lemma 6.1** (Kakade–Langford, ICML 2002, p. 6). For any policies `π̃` and `π` and any
starting state distribution `μ`,
`η_μ(π̃) - η_μ(π) = (1/(1-γ)) E_{(a,s) ∼ π̃ d_{π̃,μ}}[A_π(s, a)]`.
The states are weighted by `d_{π̃,μ}`, the discounted future state distribution of the **new**
policy `π̃`, and the actions by `π̃`; the advantage is that of the old policy `π`.
In Lean, `πt` stands for the paper's `π̃`.
Standing assumptions of the paper's §2: finite nonempty `S`, `A`; transition kernel `P`;
rewards in `[0, R]`; `0 ≤ γ < 1`. -/
theorem performance_difference {S A : Type} [Fintype S] [Fintype A] [DecidableEq S]
    [Nonempty S] [Nonempty A]
    (P : S → A → S → ℝ) (hP : IsTransitionKernel P)
    (r : S → A → ℝ) (R : ℝ) (hR : 0 < R) (hr : ∀ s a, 0 ≤ r s a ∧ r s a ≤ R)
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (μ : S → ℝ) (hμ : IsStateDist μ)
    (πt π : S → A → ℝ) (hπt : IsPolicy πt) (hπ : IsPolicy π) :
    eta P r γ πt μ - eta P r γ π μ =
      1 / (1 - γ) * ∑ s, futureStateDist P γ πt μ s * ∑ a, πt s a * advantage P r γ π s a := by sorry

end ApproxOptRL.CPI
