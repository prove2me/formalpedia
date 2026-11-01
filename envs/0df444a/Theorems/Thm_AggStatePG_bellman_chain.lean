-- Prove2me | Theorems.Thm_AggStatePG_bellman_chain
-- name    : AggStatePG.bellman_chain
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T12:43:44.787017+00:00
-- url     : https://prove2.me/theorems/40f60d81-f753-451a-b4d3-09b50641aa45
-- title:
--   Proof of Theorem 3, p.11: $V\succeq TV-ce$ implies $V\succeq V^*-\frac{c}{1-\gamma}e$
-- statement:
--   Throughout, $M=(\mathcal S,\mathcal A,r,P,\gamma,\rho)$ is a finite Markov decision process: finite state and action sets, a real reward $r(s,a)$ (no bound), transition probabilities $P(s'\mid s,a)$, a discount factor $\gamma\in(0,1)$ and an initial distribution $\rho$ on $\mathcal S$. $\Pi$ is the set of stationary randomized policies $\pi:\mathcal S\to\Delta(\mathcal A)$, $V_\pi$ the value function of $\pi$, $Q_\pi(s,a)=r(s,a)+\gamma\sum_{s'}P(s'\mid s,a)V_\pi(s')$, $V^*(s)=\max_{\pi\in\Pi}V_\pi(s)$, $J(\pi)=(1-\gamma)\sum_s\rho(s)V_\pi(s)$ and $\eta_\pi=(1-\gamma)\sum_{t\ge0}\gamma^t\rho P_\pi^t$ the discounted state occupancy measure.
--
--   For every value function $V\in\mathbb R^{\mathcal S}$ and every real $c$: if $V\succeq TV-ce$ element-wise, then
--   $$V\succeq V^*-\frac{c}{1-\gamma}e.$$
--
--   With $V=V_{\pi_\infty}$ and $c=2\epsilon_\phi$ this is the chain
--   $$V_{\pi_\infty}\succeq TV_{\pi_\infty}-2\epsilon_\phi e\succeq T^2V_{\pi_\infty}+2\gamma\epsilon_\phi e-2\epsilon_\phi e\succeq\cdots\succeq V^*-\frac{2\epsilon_\phi}{1-\gamma}e$$
--   that ends the proof of Theorem 3.
--
--   Differences from the source:
--   - generalization: V = V_π∞ and c = 2ϵφ → every V : S → ℝ and every real c with V ⪰ TV − ce; reason: the chain uses V_π∞ and 2ϵφ only through V_π∞ ⪰ TV_π∞ − 2ϵφe; the page's case is an instance
--   - encoding: finite action space A = {1, …, |A|} → a finite nonempty action type ([Nonempty A]); reason: Δ(A) and Π are empty for an empty action set; the paper's MDP has policies (an optimal one exists, p.4)
--   - encoding: V*(s) = max_{π∈Π} V_π(s) → Vstar = sSup of {V_π(s) : π ∈ Π}; reason: the set is bounded and the maximum is attained (an optimal policy exists, p.4), so sSup is the maximum
--   - encoding: TV(s) = max_{d∈Δ(A)} [r(s,d) + γ Σ_{s′} P(s′|s,d)V(s′)] → bellmanOpt = sSup of the image of Δ(A); reason: for nonempty finite A the image is a nonempty compact set, so sSup is the maximum
-- source:
--   Russo, Approximation Benefits of Policy Gradient Methods with Aggregated States, arXiv:2007.11684v3, proof of Theorem 3, final display, p.11

import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_IsTransitionKernel
import Definitions.Def_AggStatePG_bellmanOpt
import Definitions.Def_AggStatePG_Vstar

open FoundationsML.ReinforcementLearning

namespace AggStatePG

/-- **The final chain of the proof of Theorem 3** (Russo, *Approximation Benefits of Policy Gradient Methods with Aggregated States*, arXiv:2007.11684v3, proof of Theorem 3, p.11):
`V_{π_∞} ⪰ TV_{π_∞} - 2ϵ_φ e ⪰ T²V_{π_∞} + 2γϵ_φ e - 2ϵ_φ e ⪰ ⋯ ⪰ V* - (2ϵ_φ/(1-γ)) e`.
In general form: for every `V : S → ℝ` and every real `c`, if `V ⪰ TV - ce` then
`V ⪰ V* - (c/(1-γ)) e`.

**Formalization Note.** `T = bellmanOpt`, `V* = Vstar`. The chain uses `V` and `c` only through the
hypothesis `V ⪰ TV - ce`; the page's instance is `V = V_{π_∞}`, `c = 2ϵ_φ`. The action type is
nonempty. -/
theorem bellman_chain {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A] [Nonempty A]
    (P : S → A → S → ℝ) (hP : IsTransitionKernel P) (r : S → A → ℝ)
    (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1) (V : S → ℝ) (c : ℝ)
    (hV : ∀ s : S, bellmanOpt P r γ V s - c ≤ V s) :
    ∀ s : S, Vstar P r γ s - c / (1 - γ) ≤ V s := by sorry

end AggStatePG
