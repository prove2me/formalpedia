-- Prove2me | Theorems.Thm_AggStatePG_lemma_6
-- name    : AggStatePG.lemma_6
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T12:44:44.180992+00:00
-- url     : https://prove2.me/theorems/fde66713-95ab-4137-a794-1edabbdeada0
-- title:
--   Lemma 6, p.10: an approximate Bellman equation for stationary points (corrected: π∞ ∈ Πφ)
-- statement:
--   Throughout, $M=(\mathcal S,\mathcal A,r,P,\gamma,\rho)$ is a finite Markov decision process: finite state and action sets, a real reward $r(s,a)$ (no bound), transition probabilities $P(s'\mid s,a)$, a discount factor $\gamma\in(0,1)$ and an initial distribution $\rho$ on $\mathcal S$. $\Pi$ is the set of stationary randomized policies $\pi:\mathcal S\to\Delta(\mathcal A)$, $V_\pi$ the value function of $\pi$, $Q_\pi(s,a)=r(s,a)+\gamma\sum_{s'}P(s'\mid s,a)V_\pi(s')$, $V^*(s)=\max_{\pi\in\Pi}V_\pi(s)$, $J(\pi)=(1-\gamma)\sum_s\rho(s)V_\pi(s)$ and $\eta_\pi=(1-\gamma)\sum_{t\ge0}\gamma^t\rho P_\pi^t$ the discounted state occupancy measure.
--
--   A state aggregation $\phi$ partitions $\mathcal S$ into segments $\mathcal S_i=\phi^{-1}(i)$; $\Pi_\phi=\{\pi\in\Pi:\pi(s)=\pi(s')\text{ whenever }\phi(s)=\phi(s')\}$ is the state-aggregated policy class.
--
--   If $\pi_\infty\in\Pi_\phi$ is a first order stationary point of $J(\cdot)$ on $\Pi_\phi$ (Definition 1), then
--   $$\mathbb E[V_{\pi_\infty}(S)]=\max_{\pi\in\Pi_\phi}\mathbb E\big[T_\pi V_{\pi_\infty}(S)\big]\qquad\text{where }S\sim\eta_{\pi_\infty},\qquad(9)$$
--   and the maximum is attained (at $\pi=\pi_\infty$).
--
--   Within the restricted class, a stationary point satisfies the Bellman equation on average under its own occupancy measure. The proof of Theorem 3 decomposes this maximization across segments.
--
--   **Formalization Note** $\mathbb E[f(S)]=\sum_s\eta_{\pi_\infty}(s)f(s)$; "max" is stated as `IsGreatest` (attained, and an upper bound).
--
--   Differences from the source:
--   - correction: π∞ a stationary point of J on Πφ in the sense of Definition 1 (π∞ ∈ Π) → π∞ ∈ Πφ (hmem) and stationary in the sense of Definition 1; reason: with π∞ ∈ Π only the lemma is false: on the 3-state, 1-segment instance of Theorem 3's note (γ=9/10, ρ=(1/50,1/2,12/25)) the stationary π∞=(α,α,β) ∉ Πφ has max_{π∈Πφ} E[T_πV_π∞(S)] − E[V_π∞(S)] = −1/5; the proof on p.10 says it uses π∞ ∈ Πφ
--   - encoding: max over π ∈ Πφ → IsGreatest of the set of values; reason: the paper's max is attained (at π∞); IsGreatest states attainment and the upper bound
--   - encoding: ∇J(π) for J : Π → ℝ, policies stacked in ℝ^{|S|·|A|} → gradient of Jext = (1−γ)·directValue on EuclideanSpace ℝ (S × A); reason: Jext equals J on Π and is differentiable at every point of Π (Lemma 5), so its gradient is the paper's ∇J
--   - generalization: φ : S → {1,…,m} → φ : S → ι for any type ι; reason: ι = Fin m is the printed case; the labels play no other role
-- source:
--   Russo, Approximation Benefits of Policy Gradient Methods with Aggregated States, arXiv:2007.11684v3, Lemma 6, display (9), p.10

import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_IsTransitionKernel
import Definitions.Def_FoundationsML_ReinforcementLearning_PolicyValue
import Definitions.Def_PolicyGradTheory_ProjGA_MDP
import Definitions.Def_PolicyGradTheory_ProjGA_Algorithm
import Definitions.Def_AggStatePG_bellmanPol
import Definitions.Def_AggStatePG_aggSet
import Definitions.Def_AggStatePG_IsFirstOrderStationary

open FoundationsML.ReinforcementLearning PolicyGradTheory.ProjGA

namespace AggStatePG

/-- **Lemma 6** (An approximate Bellman equation for stationary points; Russo, *Approximation Benefits of Policy Gradient Methods with Aggregated States*, arXiv:2007.11684v3, Lemma 6, p.10),
corrected: `π_∞ ∈ Π_φ`. If `π_∞ ∈ Π_φ` is a stationary point of `J(·)` on `Π_φ`, then
`E[V_{π_∞}(S)] = max_{π ∈ Π_φ} E[T_π V_{π_∞}(S)]` where `S ∼ η_{π_∞}`. (9)
The maximum is attained (at `π = π_∞`).

**Formalization Note.** `E[f(S)] = ∑_s η_{π_∞}(s) f(s)`, `η = visitation`; `max` is `IsGreatest`
(attained and an upper bound). Definition 1 allows a stationary point in `Π`; the proof on p.10 uses
`π_∞ ∈ Π_φ`, and without it the lemma is false (a 3-state, 1-segment instance gives
`max_{π∈Π_φ} E[T_π V_{π_∞}] - E[V_{π_∞}] = -1/5`), so `π_∞ ∈ Π_φ` is a hypothesis. -/
theorem lemma_6 {S A ι : Type*} [Fintype S] [DecidableEq S] [Fintype A]
    (P : S → A → S → ℝ) (hP : IsTransitionKernel P) (r : S → A → ℝ)
    (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1) (ρ : S → ℝ) (hρ : IsDist ρ) (φ : S → ι)
    (πinf : EuclideanSpace ℝ (S × A)) (hmem : πinf ∈ aggSet φ)
    (hstat : IsFirstOrderStationary P r γ ρ (aggSet φ) πinf) :
    IsGreatest
      {v : ℝ | ∃ x ∈ (aggSet φ : Set (EuclideanSpace ℝ (S × A))),
        v = ∑ s : S, visitation (asPolicy πinf) P γ ρ s *
          bellmanPol (asPolicy x) P r γ (fun s' => PolicyValue (asPolicy πinf) P r γ s') s}
      (∑ s : S, visitation (asPolicy πinf) P γ ρ s * PolicyValue (asPolicy πinf) P r γ s) := by sorry

end AggStatePG
