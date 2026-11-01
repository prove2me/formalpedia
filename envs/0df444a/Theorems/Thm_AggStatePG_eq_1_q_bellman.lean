-- Prove2me | Theorems.Thm_AggStatePG_eq_1_q_bellman
-- name    : AggStatePG.eq_1_q_bellman
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T12:43:42.529371+00:00
-- url     : https://prove2.me/theorems/34735649-8598-4ead-9441-477423b59fbf
-- title:
--   Relations (1), p.5: $Q_\pi(s,\pi'(s))=(T_{\pi'}V_\pi)(s)$ and $\max_d Q_\pi(s,d)=(TV_\pi)(s)$
-- statement:
--   Throughout, $M=(\mathcal S,\mathcal A,r,P,\gamma,\rho)$ is a finite Markov decision process: finite state and action sets, a real reward $r(s,a)$ (no bound), transition probabilities $P(s'\mid s,a)$, a discount factor $\gamma\in(0,1)$ and an initial distribution $\rho$ on $\mathcal S$. $\Pi$ is the set of stationary randomized policies $\pi:\mathcal S\to\Delta(\mathcal A)$, $V_\pi$ the value function of $\pi$, $Q_\pi(s,a)=r(s,a)+\gamma\sum_{s'}P(s'\mid s,a)V_\pi(s')$, $V^*(s)=\max_{\pi\in\Pi}V_\pi(s)$, $J(\pi)=(1-\gamma)\sum_s\rho(s)V_\pi(s)$ and $\eta_\pi=(1-\gamma)\sum_{t\ge0}\gamma^t\rho P_\pi^t$ the discounted state occupancy measure.
--
--   For all policies $\pi,\pi'\in\Pi$ and every state $s$:
--
--   1. $Q_\pi(s,\pi'(s))=(T_{\pi'}V_\pi)(s)$;
--   2. $\displaystyle\max_{d\in\Delta(\mathcal A)}Q_\pi(s,d)=(TV_\pi)(s)$;
--   3. for every value function $V$, $\displaystyle TV(s)=\max_{a\in\mathcal A}\Big[r(s,a)+\gamma\sum_{s'}P(s'\mid s,a)V(s')\Big]$; in particular $\max_{a}Q_\pi(s,a)=TV_\pi(s)$, the observation used in the proof of Theorem 3 (p.11).
--
--   These relations translate between $Q$ functions and Bellman operators throughout the proofs of Lemma 6 and Theorem 3.
--
--   **Formalization Note** $T$ is a supremum over $\Delta(\mathcal A)$ (`bellmanOpt`), $T_\pi$ is `bellmanPol`, $Q_\pi(s,d)$ is `qDist`.
--
--   Differences from the source:
--   - generalization: (1): the two relations → the two relations and a third clause, TV(s) = max_a [r(s,a) + γ Σ P V], for every V; reason: the third clause is the observation max_a Q_π∞(s,a) = TV_π∞(s) of p.11; dropping it gives (1)
--   - encoding: finite action space A = {1, …, |A|} → a finite nonempty action type ([Nonempty A]); reason: Δ(A) and Π are empty for an empty action set; the paper's MDP has policies (an optimal one exists, p.4)
--   - encoding: max over d ∈ Δ(A), in T and in (1) → sSup of the image of Δ(A) (bellmanOpt, and the left side of clause 2); reason: for nonempty finite A the image is a nonempty compact set, so sSup is the maximum
-- source:
--   Russo, Approximation Benefits of Policy Gradient Methods with Aggregated States, arXiv:2007.11684v3, display (1), p.5; clause 3: proof of Theorem 3, p.11

import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_IsPolicy
import Definitions.Def_FoundationsML_ReinforcementLearning_IsTransitionKernel
import Definitions.Def_FoundationsML_ReinforcementLearning_PolicyValue
import Definitions.Def_PolicyGradTheory_ProjGA_MDP
import Definitions.Def_AggStatePG_bellmanPol
import Definitions.Def_AggStatePG_bellmanOpt
import Definitions.Def_AggStatePG_qDist

open FoundationsML.ReinforcementLearning PolicyGradTheory.ProjGA

namespace AggStatePG

/-- **Relations (1)** between `Q` functions and Bellman operators (Russo, *Approximation Benefits of Policy Gradient Methods with Aggregated States*, arXiv:2007.11684v3, display (1), p.5),
together with the identity `max_{a ∈ A} Q_π(s,a) = TV_π(s)` used in the proof of Theorem 3 (p.11).
For policies `π, π' ∈ Π` and every state `s`:
1. `Q_π(s, π'(s)) = (T_{π'} V_π)(s)`;
2. `max_{d ∈ Δ(A)} Q_π(s, d) = (T V_π)(s)`;
3. for every `V`, `TV(s) = max_{a ∈ A} [r(s,a) + γ ∑_{s'} P(s'|s,a) V(s')]`; in particular
   `max_a Q_π(s,a) = TV_π(s)`.

**Formalization Note.** `Q_π(s,d) = qDist`, `T_π = bellmanPol`, `T = bellmanOpt` (a supremum over
`Δ(A)`), `V_π = PolicyValue`. The action type is nonempty (the paper's `A = {1, …, |A|}` carries
policies). The maximum over `Δ(A)` is written `sSup`. -/
theorem eq_1_q_bellman {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A] [Nonempty A]
    (P : S → A → S → ℝ) (hP : IsTransitionKernel P) (r : S → A → ℝ)
    (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    (∀ π π' : S → A → ℝ, IsPolicy π → IsPolicy π' → ∀ s : S,
        qDist π P r γ s (π' s) = bellmanPol π' P r γ (fun s' => PolicyValue π P r γ s') s) ∧
    (∀ π : S → A → ℝ, IsPolicy π → ∀ s : S,
        sSup (qDist π P r γ s '' {d : A → ℝ | IsDist d}) =
          bellmanOpt P r γ (fun s' => PolicyValue π P r γ s') s) ∧
    (∀ (V : S → ℝ) (s : S), bellmanOpt P r γ V s =
        Finset.univ.sup' Finset.univ_nonempty
          (fun a : A => r s a + γ * ∑ s' : S, P s a s' * V s')) := by sorry

end AggStatePG
