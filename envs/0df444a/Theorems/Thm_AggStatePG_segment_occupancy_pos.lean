-- Prove2me | Theorems.Thm_AggStatePG_segment_occupancy_pos
-- name    : AggStatePG.segment_occupancy_pos
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T12:43:04.20256+00:00
-- url     : https://prove2.me/theorems/c0197011-3e22-4e69-8b68-b7092286f720
-- title:
--   Proof of Theorem 3, p.11: every segment has positive occupancy, $\mathbb P(S\in\mathcal S_i)>0$
-- statement:
--   Throughout, $M=(\mathcal S,\mathcal A,r,P,\gamma,\rho)$ is a finite Markov decision process: finite state and action sets, a real reward $r(s,a)$ (no bound), transition probabilities $P(s'\mid s,a)$, a discount factor $\gamma\in(0,1)$ and an initial distribution $\rho$ on $\mathcal S$. $\Pi$ is the set of stationary randomized policies $\pi:\mathcal S\to\Delta(\mathcal A)$, $V_\pi$ the value function of $\pi$, $Q_\pi(s,a)=r(s,a)+\gamma\sum_{s'}P(s'\mid s,a)V_\pi(s')$, $V^*(s)=\max_{\pi\in\Pi}V_\pi(s)$, $J(\pi)=(1-\gamma)\sum_s\rho(s)V_\pi(s)$ and $\eta_\pi=(1-\gamma)\sum_{t\ge0}\gamma^t\rho P_\pi^t$ the discounted state occupancy measure.
--
--   A state aggregation $\phi$ partitions $\mathcal S$ into segments $\mathcal S_i=\phi^{-1}(i)$; $\Pi_\phi=\{\pi\in\Pi:\pi(s)=\pi(s')\text{ whenever }\phi(s)=\phi(s')\}$ is the state-aggregated policy class.
--
--   For every policy $\pi\in\Pi$:
--
--   1. $\eta_\pi(s)\ge(1-\gamma)\rho(s)$ for every state $s$;
--   2. if every segment has positive initial mass, $\rho(\mathcal S_i)>0$, then every segment has positive occupancy, $\eta_\pi(\mathcal S_i)>0$, i.e. $\mathbb P(S\in\mathcal S_i)>0$ for $S\sim\eta_\pi$.
--
--   The proof of Theorem 3 uses the second clause for $\pi=\pi_\infty$: "Here we use implicitly that $\mathbb P(S\in\mathcal S_i)>0$, which is assured by our assumption that $\rho(\mathcal S_i)>0$."
--
--   **Formalization Note** Segments are the fibres of $\phi:\mathcal S\to\iota$; positivity is required for the segment of every state.
--
--   Differences from the source:
--   - generalization: P(S ∈ S_i) > 0 for S ∼ η_π∞ → for every policy π: η_π ≥ (1−γ)ρ, and positive ρ-mass on every segment gives positive η_π-mass on every segment; reason: π∞ is a policy, and the first clause is the fact behind 'assured by'; specializing π := π∞ and dropping clause 1 gives the page's claim
--   - generalization: φ : S → {1,…,m} with ρ(φ⁻¹(i)) > 0 for each i → φ : S → ι with positive ρ-mass on the segment of every state; reason: for ι = Fin m the printed hypothesis implies this one; the labels play no other role
-- source:
--   Russo, Approximation Benefits of Policy Gradient Methods with Aggregated States, arXiv:2007.11684v3, proof of Theorem 3, p.11

import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_IsPolicy
import Definitions.Def_FoundationsML_ReinforcementLearning_IsTransitionKernel
import Definitions.Def_PolicyGradTheory_ProjGA_MDP

open FoundationsML.ReinforcementLearning PolicyGradTheory.ProjGA

namespace AggStatePG

/-- **Positive occupancy of every segment** (Russo, *Approximation Benefits of Policy Gradient Methods with Aggregated States*, arXiv:2007.11684v3, proof of Theorem 3, p.11): "Here we use
implicitly that `P(S ∈ S_i) > 0`, which is assured by our assumption that `ρ(S_i) > 0`", where
`S ∼ η_{π_∞}` and `S_i = φ^{-1}(i)`. For every policy `π`:
1. `η_π(s) ≥ (1-γ) ρ(s)` for every state `s` (the fact behind "assured by");
2. if every segment has positive `ρ`-mass, every segment has positive `η_π`-mass.

**Formalization Note.** `η_π = visitation`. Segments are the fibres `{s' : φ s' = φ s}` of
`φ : S → ι`; "`ρ(φ^{-1}(i)) > 0` for each `i`" is written for each nonempty segment, i.e. for the
segment of every state `s`. -/
theorem segment_occupancy_pos {S A ι : Type*} [Fintype S] [DecidableEq S] [Fintype A]
    [DecidableEq ι] (P : S → A → S → ℝ) (hP : IsTransitionKernel P)
    (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1) (ρ : S → ℝ) (hρ : IsDist ρ) (φ : S → ι)
    (π : S → A → ℝ) (hπ : IsPolicy π) :
    (∀ s : S, (1 - γ) * ρ s ≤ visitation π P γ ρ s) ∧
    ((∀ s : S, 0 < ∑ s' ∈ Finset.univ.filter (fun s' => φ s' = φ s), ρ s') →
      ∀ s : S, 0 < ∑ s' ∈ Finset.univ.filter (fun s' => φ s' = φ s), visitation π P γ ρ s') := by sorry

end AggStatePG
