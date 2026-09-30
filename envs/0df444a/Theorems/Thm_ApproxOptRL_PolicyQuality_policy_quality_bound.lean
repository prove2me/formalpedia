-- Prove2me | Theorems.Thm_ApproxOptRL_PolicyQuality_policy_quality_bound
-- name    : ApproxOptRL.PolicyQuality.policy_quality_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-29T17:02:24.884846+00:00
-- url     : https://prove2.me/theorems/aaa64754-caf1-4532-aa6f-4aa5057c7db8
-- title:
--   Theorem 6.2 — $\eta_{\tilde\mu}(\pi^*)-\eta_{\tilde\mu}(\pi)\le\frac{\varepsilon}{1-\gamma}\|d_{\pi^*,\tilde\mu}/d_{\pi,\mu}\|_\infty$ when $\mathrm{OPT}(\mathbb A_{\pi,\mu})<\varepsilon$
-- statement:
--   This is the near-optimality guarantee of Kakade and Langford for a policy whose optimal policy advantage is small.
--
--   Consider a finite MDP with states $S$, actions $A$, transition probabilities $P(s';s,a)$, rewards $\mathcal R(s,a)\in[0,R]$ with $R>0$, and discount factor $0\le\gamma<1$. Write $V_\pi$ for the normalized value function, $d_{\pi,\mu}$ for the $\gamma$-discounted future state distribution of $\pi$ from the start distribution $\mu$, $\eta_\mu(\pi)=E_{s\sim\mu}[V_\pi(s)]$, and $\mathrm{OPT}(\mathbb A_{\pi,\mu})=\max_{\pi'}\mathbb A_{\pi,\mu}(\pi')$ for the largest policy advantage over $\pi$ under the restart distribution $\mu$. For a ratio of nonnegative functions, $\|f/g\|_\infty=\max_s f(s)/g(s)$.
--
--   Let $\mu$ be a state distribution and $\pi$ a stochastic policy with $\mathrm{OPT}(\mathbb A_{\pi,\mu})<\varepsilon$, and let $\pi^*$ be an optimal policy. Then for every state distribution $\tilde\mu$,
--   $$\eta_{\tilde\mu}(\pi^*)-\eta_{\tilde\mu}(\pi)\le\frac{\varepsilon}{1-\gamma}\left\|\frac{d_{\pi^*,\tilde\mu}}{d_{\pi,\mu}}\right\|_\infty\le\frac{\varepsilon}{(1-\gamma)^2}\left\|\frac{d_{\pi^*,\tilde\mu}}{\mu}\right\|_\infty.$$
--
--   Concretely, the statement has three parts:
--   1. if $d_{\pi^*,\tilde\mu}(s)\le C\,d_{\pi,\mu}(s)$ for every $s$, then $\eta_{\tilde\mu}(\pi^*)-\eta_{\tilde\mu}(\pi)\le\frac{\varepsilon}{1-\gamma}C$;
--   2. if $d_{\pi^*,\tilde\mu}(s)\le C\,\mu(s)$ for every $s$, then $d_{\pi^*,\tilde\mu}(s)\le\frac{C}{1-\gamma}\,d_{\pi,\mu}(s)$ for every $s$ (the middle inequality, $\|d_{\pi^*,\tilde\mu}/d_{\pi,\mu}\|_\infty\le\frac1{1-\gamma}\|d_{\pi^*,\tilde\mu}/\mu\|_\infty$);
--   3. if $d_{\pi^*,\tilde\mu}(s)\le C\,\mu(s)$ for every $s$, then $\eta_{\tilde\mu}(\pi^*)-\eta_{\tilde\mu}(\pi)\le\frac{\varepsilon}{(1-\gamma)^2}C$.
--
--   The theorem quantifies how good the policy returned by conservative policy iteration is: a small policy advantage with respect to the restart distribution $\mu$ gives near-optimal performance with respect to any other distribution $\tilde\mu$, at a cost measured by the mismatch between $\tilde\mu$'s optimal future state distribution and $\mu$.
--
--   **Formalization Note** The ratio norms are encoded multiplicatively: "$X\le K\|f/g\|_\infty$" becomes "$X\le K\,C$ for every $C$ with $f\le C g$ pointwise". The least such $C$ is $\max_s f(s)/g(s)$ when $g>0$; if $g(s)=0<f(s)$ for some $s$, no $C$ exists, matching $\|f/g\|_\infty=+\infty$; a state with $f(s)=g(s)=0$ imposes nothing. No full-support assumption on $\mu$ or $\tilde\mu$ is made. $\mathrm{OPT}$ is the supremum over stochastic policies. The standing assumptions of the paper's §2 (finite nonempty $S$, $A$; $P$ a kernel; rewards in $[0,R]$; $0\le\gamma<1$; $\pi$ stochastic; $\mu$, $\tilde\mu$ distributions) are explicit hypotheses. In Lean, `πstar` is $\pi^*$ and `μ'` is $\tilde\mu$.
-- source:
--   Kakade, Langford, Approximately Optimal Approximate Reinforcement Learning, ICML 2002, p. 6, Theorem 6.2 (proof p. 7); l_∞-norm of ratios as defined on p. 5

import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_IsTransitionKernel
import Definitions.Def_FoundationsML_ReinforcementLearning_IsPolicy
import Definitions.Def_ApproxOptRL_Shared_Model
import Definitions.Def_ApproxOptRL_PolicyQuality_PolicyAdvantage
open ApproxOptRL.Shared
open FoundationsML.ReinforcementLearning

namespace ApproxOptRL.PolicyQuality

/-- **Theorem 6.2** (Kakade–Langford, ICML 2002, p. 6). Assume that for a policy `π`,
`OPT(𝔸_{π,μ}) < ε`. Let `π*` (`πstar`) be an optimal policy. Then for any state distribution
`μ̃` (`μ'`),
`η_μ̃(π*) - η_μ̃(π) ≤ ε/(1-γ) ‖d_{π*,μ̃}/d_{π,μ}‖_∞ ≤ ε/(1-γ)² ‖d_{π*,μ̃}/μ‖_∞`.

The `l_∞`-norm of a ratio, `‖f/g‖_∞ = max_s f(s)/g(s)` (p. 5), is encoded multiplicatively:
a bound `X ≤ K ‖f/g‖_∞` is stated as `X ≤ K * C` for every `C` with `f s ≤ C * g s` for all
`s`. When some `g s = 0 < f s` no such `C` exists (the norm is `+∞` and the bound is empty);
a state with `f s = g s = 0` imposes nothing. The three conjuncts are the first inequality, the
middle comparison `‖d_{π*,μ̃}/d_{π,μ}‖_∞ ≤ (1/(1-γ)) ‖d_{π*,μ̃}/μ‖_∞`, and the outer bound.
Standing assumptions of the paper's §2: finite nonempty `S`, `A`; transition kernel `P`;
rewards in `[0, R]`; `0 ≤ γ < 1`. -/
theorem policy_quality_bound {S A : Type} [Fintype S] [Fintype A] [DecidableEq S]
    [Nonempty S] [Nonempty A]
    (P : S → A → S → ℝ) (hP : IsTransitionKernel P)
    (r : S → A → ℝ) (R : ℝ) (hR : 0 < R) (hr : ∀ s a, 0 ≤ r s a ∧ r s a ≤ R)
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (μ : S → ℝ) (hμ : IsStateDist μ)
    (π : S → A → ℝ) (hπ : IsPolicy π)
    (ε : ℝ) (h : optPolicyAdvantage P r γ π μ < ε)
    (πstar : S → A → ℝ) (hπstar : IsOptimalPolicy P r γ πstar)
    (μ' : S → ℝ) (hμ' : IsStateDist μ') :
    (∀ C : ℝ, (∀ s, futureStateDist P γ πstar μ' s ≤ C * futureStateDist P γ π μ s) →
        eta P r γ πstar μ' - eta P r γ π μ' ≤ ε / (1 - γ) * C) ∧
    (∀ C : ℝ, (∀ s, futureStateDist P γ πstar μ' s ≤ C * μ s) →
        ∀ s, futureStateDist P γ πstar μ' s ≤ C / (1 - γ) * futureStateDist P γ π μ s) ∧
    (∀ C : ℝ, (∀ s, futureStateDist P γ πstar μ' s ≤ C * μ s) →
        eta P r γ πstar μ' - eta P r γ π μ' ≤ ε / (1 - γ) ^ 2 * C) := by sorry

end ApproxOptRL.PolicyQuality
