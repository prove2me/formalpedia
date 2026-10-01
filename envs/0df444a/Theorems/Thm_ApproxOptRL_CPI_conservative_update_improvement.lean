-- Prove2me | Theorems.Thm_ApproxOptRL_CPI_conservative_update_improvement
-- name    : ApproxOptRL.CPI.conservative_update_improvement
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T10:45:16.095986+00:00
-- url     : https://prove2.me/theorems/d6629ffd-4585-4edb-a1bd-64c4f6be109c
-- title:
--   Theorem 4.1 — improvement bound for the conservative update $\pi_{new}=(1-\alpha)\pi+\alpha\pi'$
-- statement:
--   Consider a finite MDP with nonempty state set $S$, nonempty action set $A$, transition probabilities $P(s';s,a)$, rewards $\mathcal R(s,a)\in[0,R]$ with $R>0$, and discount factor $0\le\gamma<1$; let $\mu$ be a state distribution and let $\pi$, $\pi'$ be policies.
--
--   Let $\mathbb A = \mathbb A_{\pi,\mu}(\pi')$ be the policy advantage of $\pi'$ with respect to $\pi$ and $\mu$, and let
--   $$\varepsilon = \max_s\big|E_{a\sim\pi'(a;s)}[A_\pi(s,a)]\big|.$$
--   For the update rule (4.1), $\pi_{new}(a;s) = (1-\alpha)\pi(a;s)+\alpha\pi'(a;s)$, and for all $\alpha\in[0,1]$:
--   $$\eta_\mu(\pi_{new}) - \eta_\mu(\pi) \ge \frac{\alpha}{1-\gamma}\left(\mathbb A - \frac{2\alpha\gamma\varepsilon}{1-\gamma(1-\alpha)}\right).$$
--
--   The first term is the first-order gain $\frac{\alpha}{1-\gamma}\mathbb A$ and the second a penalty for the state distribution of $\pi_{new}$ differing from $d_{\pi,\mu}$. For small $\alpha$ the bound guarantees improvement whenever the policy advantage is positive; it is the step on which conservative policy iteration rests.
--
--   **Formalization Note** $\varepsilon$ is a quantity local to this theorem (the maximum over all states, written as `Finset.sup'`), unrelated to the accuracy of a greedy chooser. The denominator $1-\gamma(1-\alpha)$ is positive under $0\le\gamma<1$, $\alpha\in[0,1]$.
-- source:
--   Kakade, Langford, Approximately Optimal Approximate Reinforcement Learning, ICML 2002, p. 4, Theorem 4.1 (proof p. 8, appendix §8)

import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_IsTransitionKernel
import Definitions.Def_FoundationsML_ReinforcementLearning_IsPolicy
import Definitions.Def_ApproxOptRL_Shared_Model
import Definitions.Def_ApproxOptRL_CPI_PolicyAdvantage
open ApproxOptRL.Shared
open FoundationsML.ReinforcementLearning

namespace ApproxOptRL.CPI

/-- **Theorem 4.1** (Kakade–Langford, ICML 2002, p. 4; proof p. 8). Let `𝔸 = 𝔸_{π,μ}(π')` be
the policy advantage of `π'` with respect to `π` and `μ`, and let
`ε = max_s |E_{a ∼ π'(a;s)}[A_π(s, a)]|`. For the update rule (4.1),
`π_new = (1 - α) π + α π'`, and for all `α ∈ [0, 1]`:
`η_μ(π_new) - η_μ(π) ≥ (α/(1-γ)) (𝔸 - 2αγε/(1 - γ(1 - α)))`.
Here `ε` is a quantity local to this theorem (not the accuracy of a greedy chooser).
Standing assumptions of the paper's §2: finite nonempty `S`, `A`; transition kernel `P`;
rewards in `[0, R]`; `0 ≤ γ < 1`; `μ` a state distribution. -/
theorem conservative_update_improvement {S A : Type} [Fintype S] [Fintype A] [DecidableEq S]
    [Nonempty S] [Nonempty A]
    (P : S → A → S → ℝ) (hP : IsTransitionKernel P)
    (r : S → A → ℝ) (R : ℝ) (hR : 0 < R) (hr : ∀ s a, 0 ≤ r s a ∧ r s a ≤ R)
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (μ : S → ℝ) (hμ : IsStateDist μ)
    (π π' : S → A → ℝ) (hπ : IsPolicy π) (hπ' : IsPolicy π')
    (α : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) :
    let ε : ℝ := Finset.univ.sup' Finset.univ_nonempty
      (fun s => |∑ a, π' s a * advantage P r γ π s a|)
    α / (1 - γ) * (policyAdvantage P r γ π μ π' - 2 * α * γ * ε / (1 - γ * (1 - α))) ≤
      eta P r γ (mixPolicy α π π') μ - eta P r γ π μ := by sorry

end ApproxOptRL.CPI
