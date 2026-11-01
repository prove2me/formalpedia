-- Prove2me | Theorems.Thm_AggStatePG_bellman_gap_le
-- name    : AggStatePG.bellman_gap_le
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T12:45:08.965716+00:00
-- url     : https://prove2.me/theorems/996d0eb7-350b-41b4-a932-c8ace2a9f46d
-- title:
--   Proof of Theorem 3, p.11: $V_{\pi_\infty}\succeq TV_{\pi_\infty}-2\epsilon_\phi e$
-- statement:
--   Throughout, $M=(\mathcal S,\mathcal A,r,P,\gamma,\rho)$ is a finite Markov decision process: finite state and action sets, a real reward $r(s,a)$ (no bound), transition probabilities $P(s'\mid s,a)$, a discount factor $\gamma\in(0,1)$ and an initial distribution $\rho$ on $\mathcal S$. $\Pi$ is the set of stationary randomized policies $\pi:\mathcal S\to\Delta(\mathcal A)$, $V_\pi$ the value function of $\pi$, $Q_\pi(s,a)=r(s,a)+\gamma\sum_{s'}P(s'\mid s,a)V_\pi(s')$, $V^*(s)=\max_{\pi\in\Pi}V_\pi(s)$, $J(\pi)=(1-\gamma)\sum_s\rho(s)V_\pi(s)$ and $\eta_\pi=(1-\gamma)\sum_{t\ge0}\gamma^t\rho P_\pi^t$ the discounted state occupancy measure.
--
--   A state aggregation $\phi$ partitions $\mathcal S$ into segments $\mathcal S_i=\phi^{-1}(i)$; $\Pi_\phi=\{\pi\in\Pi:\pi(s)=\pi(s')\text{ whenever }\phi(s)=\phi(s')\}$ is the state-aggregated policy class.
--
--   Suppose every segment has positive initial mass, $\rho(\mathcal S_i)>0$, let $\varepsilon$ satisfy the inequality of Definition 2 (for example $\varepsilon=\epsilon_\phi$), and let $\pi_\infty\in\Pi_\phi$ be a first order stationary point of $J$ on $\Pi_\phi$. Then, element-wise,
--   $$V_{\pi_\infty}\succeq TV_{\pi_\infty}-2\varepsilon e,$$
--   where $e$ is the vector of ones: $TV_{\pi_\infty}(s)-2\varepsilon\le V_{\pi_\infty}(s)$ for every state $s$.
--
--   The stationary point is near-greedy with respect to its own value function, with a loss of $2\epsilon_\phi$ per state; the chain at the end of the proof of Theorem 3 turns this into the bound $2\epsilon_\phi/(1-\gamma)$ against $V^*$.
--
--   Differences from the source:
--   - reading: π∞ a stationary point, described by one action per segment → π∞ ∈ Πφ (hmem) and stationary; reason: the argument on p.11 presupposes π∞ ∈ Πφ; without it the inequality fails on the instance of Theorem 3's note (V_π∞(x) = 0 < TV_π∞(x) = 10)
--   - generalization: ϵφ, the smallest scalar satisfying Definition 2's inequality → any ε with IsAggErrorBound (Definition 2's inequality); reason: ϵφ itself satisfies the inequality, so the statement specializes to the printed one
--   - generalization: π∞ deterministic (action a∞_i on segment i) → π∞ any stationary point in Πφ, randomized or not; reason: the deterministic case is an instance
--   - generalization: φ : S → {1,…,m} with ρ(φ⁻¹(i)) > 0 for each i → φ : S → ι with positive ρ-mass on the segment of every state; reason: for ι = Fin m the printed hypothesis implies this one
--   - encoding: ∇J(π) for J : Π → ℝ, policies stacked in ℝ^{|S|·|A|} → gradient of Jext = (1−γ)·directValue on EuclideanSpace ℝ (S × A); reason: Jext equals J on Π and is differentiable at every point of Π (Lemma 5), so its gradient is the paper's ∇J
--   - encoding: TV(s) = max_{d∈Δ(A)} [r(s,d) + γ Σ_{s′} P(s′|s,d)V(s′)] → bellmanOpt = sSup of the image of Δ(A); reason: for nonempty finite A the image is a nonempty compact set, so sSup is the maximum
-- source:
--   Russo, Approximation Benefits of Policy Gradient Methods with Aggregated States, arXiv:2007.11684v3, proof of Theorem 3, p.11

import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_IsTransitionKernel
import Definitions.Def_FoundationsML_ReinforcementLearning_PolicyValue
import Definitions.Def_PolicyGradTheory_ProjGA_MDP
import Definitions.Def_PolicyGradTheory_ProjGA_Algorithm
import Definitions.Def_AggStatePG_bellmanOpt
import Definitions.Def_AggStatePG_aggSet
import Definitions.Def_AggStatePG_IsFirstOrderStationary
import Definitions.Def_AggStatePG_IsAggErrorBound

open FoundationsML.ReinforcementLearning PolicyGradTheory.ProjGA

namespace AggStatePG

/-- **`V_{π_∞} ⪰ TV_{π_∞} - 2ϵ_φ e`** (Russo, *Approximation Benefits of Policy Gradient Methods with Aggregated States*, arXiv:2007.11684v3, proof of Theorem 3, p.11): "Since `s` is arbitrary,
this gives element-wise inequality `V_{π_∞} ⪰ TV_{π_∞} - 2ϵ_φ e` where `e` denotes a vector of ones."
Under the hypotheses of Theorem 3 (every segment has positive `ρ`-mass, `π_∞ ∈ Π_φ` is a stationary
point of `J` on `Π_φ`, `ε` bounds the within-segment `Q`-gaps over `Π_φ`):
`TV_{π_∞}(s) - 2ε ≤ V_{π_∞}(s)` for every state `s`.

**Formalization Note.** `T = bellmanOpt`, `V_π = PolicyValue`. `ε` is any number satisfying the
inequality of Definition 2 (`IsAggErrorBound`), in particular `ϵ_φ`. `π_∞` may be randomized. -/
theorem bellman_gap_le {S A ι : Type*} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq ι]
    (P : S → A → S → ℝ) (hP : IsTransitionKernel P) (r : S → A → ℝ)
    (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1) (ρ : S → ℝ) (hρ : IsDist ρ) (φ : S → ι)
    (hseg : ∀ s : S, 0 < ∑ s' ∈ Finset.univ.filter (fun s' => φ s' = φ s), ρ s')
    (ε : ℝ) (hε : IsAggErrorBound P r γ φ ε)
    (πinf : EuclideanSpace ℝ (S × A)) (hmem : πinf ∈ aggSet φ)
    (hstat : IsFirstOrderStationary P r γ ρ (aggSet φ) πinf) :
    ∀ s : S, bellmanOpt P r γ (fun s' => PolicyValue (asPolicy πinf) P r γ s') s - 2 * ε ≤
      PolicyValue (asPolicy πinf) P r γ s := by sorry

end AggStatePG
