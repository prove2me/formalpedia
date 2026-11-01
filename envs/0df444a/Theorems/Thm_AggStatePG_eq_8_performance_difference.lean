-- Prove2me | Theorems.Thm_AggStatePG_eq_8_performance_difference
-- name    : AggStatePG.eq_8_performance_difference
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T12:43:50.317871+00:00
-- url     : https://prove2.me/theorems/f999bbbc-cd54-43d5-aa75-e2dc8c71c70e
-- title:
--   (8), first equality, p.10: the performance difference lemma
-- statement:
--   Throughout, $M=(\mathcal S,\mathcal A,r,P,\gamma,\rho)$ is a finite Markov decision process: finite state and action sets, a real reward $r(s,a)$ (no bound), transition probabilities $P(s'\mid s,a)$, a discount factor $\gamma\in(0,1)$ and an initial distribution $\rho$ on $\mathcal S$. $\Pi$ is the set of stationary randomized policies $\pi:\mathcal S\to\Delta(\mathcal A)$, $V_\pi$ the value function of $\pi$, $Q_\pi(s,a)=r(s,a)+\gamma\sum_{s'}P(s'\mid s,a)V_\pi(s')$, $V^*(s)=\max_{\pi\in\Pi}V_\pi(s)$, $J(\pi)=(1-\gamma)\sum_s\rho(s)V_\pi(s)$ and $\eta_\pi=(1-\gamma)\sum_{t\ge0}\gamma^t\rho P_\pi^t$ the discounted state occupancy measure.
--
--   For all policies $\pi,\pi'\in\Pi$,
--   $$J(\pi')-J(\pi)=\sum_{s\in\mathcal S}\sum_{a\in\mathcal A}\eta_{\pi'}(s)\big(\pi'(s,a)-\pi(s,a)\big)Q_\pi(s,a).$$
--
--   This is the performance difference lemma of Kakade and Langford (2002), the first equality of (8) in the proof sketch of Lemma 5.
--
--   **Formalization Note** $\eta_{\pi'}$ is the published `visitation`, $J$ is `objective`.
--
--   Differences from the source: none.
-- source:
--   Russo, Approximation Benefits of Policy Gradient Methods with Aggregated States, arXiv:2007.11684v3, display (8), first equality, p.10

import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_IsPolicy
import Definitions.Def_FoundationsML_ReinforcementLearning_IsTransitionKernel
import Definitions.Def_FoundationsML_ReinforcementLearning_QFunction
import Definitions.Def_PolicyGradTheory_ProjGA_MDP
import Definitions.Def_AggStatePG_objective

open FoundationsML.ReinforcementLearning PolicyGradTheory.ProjGA

namespace AggStatePG

/-- **Performance difference lemma**, the first equality of (8) (Russo, *Approximation Benefits of Policy Gradient Methods with Aggregated States*, arXiv:2007.11684v3, display (8), p.10). For
policies `π, π' ∈ Π`,
`J(π') - J(π) = ∑_{s ∈ S} ∑_{a ∈ A} η_{π'}(s) (π'(s,a) - π(s,a)) Q_π(s,a)`,
where `J(π) = (1-γ) ∑_s ρ(s) V_π(s)` (2) and `η_{π'} = (1-γ) ∑_{t ≥ 0} γ^t ρ P_{π'}^t` (p.5).

**Formalization Note.** `J = objective`, `η_π = visitation` (published, `PolicyGradTheory.ProjGA`),
`Q_π(s,a) = QFunction`. Rewards are arbitrary reals. -/
theorem eq_8_performance_difference {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]
    (P : S → A → S → ℝ) (hP : IsTransitionKernel P) (r : S → A → ℝ)
    (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1) (ρ : S → ℝ) (hρ : IsDist ρ)
    (π π' : S → A → ℝ) (hπ : IsPolicy π) (hπ' : IsPolicy π') :
    objective P r γ ρ π' - objective P r γ ρ π =
      ∑ s : S, ∑ a : A, visitation π' P γ ρ s * (π' s a - π s a) * QFunction π P r γ s a := by sorry

end AggStatePG
