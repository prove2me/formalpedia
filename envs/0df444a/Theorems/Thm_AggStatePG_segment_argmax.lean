-- Prove2me | Theorems.Thm_AggStatePG_segment_argmax
-- name    : AggStatePG.segment_argmax
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T12:44:43.758979+00:00
-- url     : https://prove2.me/theorems/fd0e007e-9787-4c36-836a-0c0d060f968d
-- title:
--   Proof of Theorem 3, p.11: the action of a stationary $\pi_\infty$ on each segment maximizes the segment-averaged $Q_{\pi_\infty}$
-- statement:
--   Throughout, $M=(\mathcal S,\mathcal A,r,P,\gamma,\rho)$ is a finite Markov decision process: finite state and action sets, a real reward $r(s,a)$ (no bound), transition probabilities $P(s'\mid s,a)$, a discount factor $\gamma\in(0,1)$ and an initial distribution $\rho$ on $\mathcal S$. $\Pi$ is the set of stationary randomized policies $\pi:\mathcal S\to\Delta(\mathcal A)$, $V_\pi$ the value function of $\pi$, $Q_\pi(s,a)=r(s,a)+\gamma\sum_{s'}P(s'\mid s,a)V_\pi(s')$, $V^*(s)=\max_{\pi\in\Pi}V_\pi(s)$, $J(\pi)=(1-\gamma)\sum_s\rho(s)V_\pi(s)$ and $\eta_\pi=(1-\gamma)\sum_{t\ge0}\gamma^t\rho P_\pi^t$ the discounted state occupancy measure.
--
--   A state aggregation $\phi$ partitions $\mathcal S$ into segments $\mathcal S_i=\phi^{-1}(i)$; $\Pi_\phi=\{\pi\in\Pi:\pi(s)=\pi(s')\text{ whenever }\phi(s)=\phi(s')\}$ is the state-aggregated policy class.
--
--   Let $\pi_\infty\in\Pi_\phi$ be a first order stationary point of $J$ on $\Pi_\phi$ and $S\sim\eta_{\pi_\infty}$. For every state $s$, with segment $\mathcal S_i\ni s$, every action $a$ with $\pi_\infty(s,a)>0$ and every action $a'$,
--   $$\sum_{s'\in\mathcal S_i}\eta_{\pi_\infty}(s')Q_{\pi_\infty}(s',a')\le\sum_{s'\in\mathcal S_i}\eta_{\pi_\infty}(s')Q_{\pi_\infty}(s',a).$$
--   That is, every action played on segment $i$ lies in $\operatorname{argmax}_{a\in\mathcal A}\mathbb E[Q_{\pi_\infty}(S,a)\mid S\in\mathcal S_i]$ when $\mathbb P(S\in\mathcal S_i)>0$. The page states this for the action $a^\infty_i$ selected by $\pi_\infty$ on segment $i$.
--
--   **Formalization Note** The sums are $\mathbb E[Q_{\pi_\infty}(S,a)\mid S\in\mathcal S_i]\,\mathbb P(S\in\mathcal S_i)$; they need no positivity hypothesis.
--
--   Differences from the source:
--   - reading: π∞ a stationary point, with 'the action selected by policy π∞ at any state s ∈ φ⁻¹(i)' → π∞ ∈ Πφ (hmem) and stationary; reason: the page's description of π∞ by one action per segment presupposes π∞ ∈ Πφ (see the correction on Theorem 3)
--   - generalization: a deterministic π∞ with action a∞_i on segment i; argmax of the conditional expectation E[Q_π∞(S,a) | S ∈ S_i] → every action a with π∞(s,a) > 0 maximizes the unconditional segment sum Σ_{s'∈S_i} η_π∞(s') Q_π∞(s',a); reason: covers randomized π∞; for deterministic π∞ and P(S ∈ S_i) > 0 dividing by P(S ∈ S_i) gives the page's argmax
--   - encoding: ∇J(π) for J : Π → ℝ, policies stacked in ℝ^{|S|·|A|} → gradient of Jext = (1−γ)·directValue on EuclideanSpace ℝ (S × A); reason: Jext equals J on Π and is differentiable at every point of Π (Lemma 5), so its gradient is the paper's ∇J
--   - generalization: φ : S → {1,…,m} → φ : S → ι for any type ι; reason: ι = Fin m is the printed case; the labels play no other role
-- source:
--   Russo, Approximation Benefits of Policy Gradient Methods with Aggregated States, arXiv:2007.11684v3, proof of Theorem 3, p.11

import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_IsTransitionKernel
import Definitions.Def_FoundationsML_ReinforcementLearning_QFunction
import Definitions.Def_PolicyGradTheory_ProjGA_MDP
import Definitions.Def_PolicyGradTheory_ProjGA_Algorithm
import Definitions.Def_AggStatePG_aggSet
import Definitions.Def_AggStatePG_IsFirstOrderStationary

open FoundationsML.ReinforcementLearning PolicyGradTheory.ProjGA

namespace AggStatePG

/-- **Per-segment argmax** (Russo, *Approximation Benefits of Policy Gradient Methods with Aggregated States*, arXiv:2007.11684v3, proof of Theorem 3, p.11): "The optimization problem above
decomposes across sates, showing `a^∞_i ∈ argmax_{a ∈ A} E[Q_{π_∞}(S,a) | S ∈ S_i]`, `i = 1, …, m`",
where `S ∼ η_{π_∞}` and `a^∞_i` is the action `π_∞` selects on segment `S_i`.

Stated for every stationary `π_∞ ∈ Π_φ`, randomized or not: every action `a` played with positive
probability on the segment of `s` maximizes `a' ↦ E[Q_{π_∞}(S,a') ; S ∈ S_i] = ∑_{s' ∈ S_i} η_{π_∞}(s')
Q_{π_∞}(s',a')` over `a' ∈ A`.

**Formalization Note.** The unconditional sum is `E[Q_{π_∞}(S,a') | S ∈ S_i] · P(S ∈ S_i)`; when
`P(S ∈ S_i) > 0` the two argmax sets coincide. `η = visitation`, `Q = QFunction`. -/
theorem segment_argmax {S A ι : Type*} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq ι]
    (P : S → A → S → ℝ) (hP : IsTransitionKernel P) (r : S → A → ℝ)
    (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1) (ρ : S → ℝ) (hρ : IsDist ρ) (φ : S → ι)
    (πinf : EuclideanSpace ℝ (S × A)) (hmem : πinf ∈ aggSet φ)
    (hstat : IsFirstOrderStationary P r γ ρ (aggSet φ) πinf)
    (s : S) (a : A) (ha : 0 < πinf (s, a)) (a' : A) :
    ∑ s' ∈ Finset.univ.filter (fun s' => φ s' = φ s),
        visitation (asPolicy πinf) P γ ρ s' * QFunction (asPolicy πinf) P r γ s' a' ≤
      ∑ s' ∈ Finset.univ.filter (fun s' => φ s' = φ s),
        visitation (asPolicy πinf) P γ ρ s' * QFunction (asPolicy πinf) P r γ s' a := by sorry

end AggStatePG
