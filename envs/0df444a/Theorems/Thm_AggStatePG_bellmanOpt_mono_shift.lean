-- Prove2me | Theorems.Thm_AggStatePG_bellmanOpt_mono_shift
-- name    : AggStatePG.bellmanOpt_mono_shift
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T12:43:50.026384+00:00
-- url     : https://prove2.me/theorems/40e47772-79f9-42f2-b336-edfdf5bf6327
-- title:
--   Proof of Theorem 3, p.11: $T$ is monotone and $T(V+ce)=TV+\gamma ce$
-- statement:
--   Throughout, $M=(\mathcal S,\mathcal A,r,P,\gamma,\rho)$ is a finite Markov decision process: finite state and action sets, a real reward $r(s,a)$ (no bound), transition probabilities $P(s'\mid s,a)$, a discount factor $\gamma\in(0,1)$ and an initial distribution $\rho$ on $\mathcal S$. $\Pi$ is the set of stationary randomized policies $\pi:\mathcal S\to\Delta(\mathcal A)$, $V_\pi$ the value function of $\pi$, $Q_\pi(s,a)=r(s,a)+\gamma\sum_{s'}P(s'\mid s,a)V_\pi(s')$, $V^*(s)=\max_{\pi\in\Pi}V_\pi(s)$, $J(\pi)=(1-\gamma)\sum_s\rho(s)V_\pi(s)$ and $\eta_\pi=(1-\gamma)\sum_{t\ge0}\gamma^t\rho P_\pi^t$ the discounted state occupancy measure.
--
--   1. If $V\preceq W$ element-wise, then $TV\preceq TW$;
--   2. for every real $c$, $T(V+ce)=TV+\gamma ce$, where $e$ is the vector of ones.
--
--   These are the two properties of the Bellman optimality operator cited from Bertsekas (1995) to iterate $V_{\pi_\infty}\succeq TV_{\pi_\infty}-2\epsilon_\phi e$.
--
--   Differences from the source:
--   - encoding: finite action space A = {1, …, |A|} → a finite nonempty action type ([Nonempty A]); reason: Δ(A) and Π are empty for an empty action set; the paper's MDP has policies (an optimal one exists, p.4)
--   - encoding: TV(s) = max_{d∈Δ(A)} [r(s,d) + γ Σ_{s′} P(s′|s,d)V(s′)] → bellmanOpt = sSup of the image of Δ(A); reason: for nonempty finite A the image is a nonempty compact set, so sSup is the maximum
-- source:
--   Russo, Approximation Benefits of Policy Gradient Methods with Aggregated States, arXiv:2007.11684v3, proof of Theorem 3, p.11

import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_IsTransitionKernel
import Definitions.Def_AggStatePG_bellmanOpt

open FoundationsML.ReinforcementLearning

namespace AggStatePG

/-- **Monotonicity and constant shift of `T`** (Russo, *Approximation Benefits of Policy Gradient Methods with Aggregated States*, arXiv:2007.11684v3, proof of Theorem 3, p.11): "Using the
monotonicity of Bellman operators and the fact that `T(V + ce) = TV + γce` [Bertsekas, 1995]".
1. If `V ⪯ W` element-wise then `TV ⪯ TW`;
2. for every real `c`, `T(V + ce) = TV + γce`, `e` the vector of ones.

**Formalization Note.** `T = bellmanOpt`. The action type is nonempty. -/
theorem bellmanOpt_mono_shift {S A : Type*} [Fintype S] [Fintype A] [Nonempty A]
    (P : S → A → S → ℝ) (hP : IsTransitionKernel P) (r : S → A → ℝ)
    (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    (∀ V W : S → ℝ, (∀ s, V s ≤ W s) → ∀ s, bellmanOpt P r γ V s ≤ bellmanOpt P r γ W s) ∧
    (∀ (V : S → ℝ) (c : ℝ) (s : S),
        bellmanOpt P r γ (fun s' => V s' + c) s = bellmanOpt P r γ V s + γ * c) := by sorry

end AggStatePG
