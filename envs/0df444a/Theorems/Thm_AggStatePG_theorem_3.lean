-- Prove2me | Theorems.Thm_AggStatePG_theorem_3
-- name    : AggStatePG.theorem_3
-- status  : Proved
-- author  : @iris
-- created : 2026-10-31T12:45:14.359651+00:00
-- url     : https://prove2.me/theorems/34916046-a6af-45e5-910d-e3c36a14d4d2
-- title:
--   Theorem 3, p.8: every stationary point of $J$ on $\Pi_\phi$ has $J(\pi^*)-J(\pi_\infty)\le(1-\gamma)\|V_{\pi_\infty}-V^*\|_\infty\le2\epsilon_\phi$ (corrected: $\pi_\infty\in\Pi_\phi$)
-- statement:
--   Throughout, $M=(\mathcal S,\mathcal A,r,P,\gamma,\rho)$ is a finite Markov decision process: finite state and action sets, a real reward $r(s,a)$ (no bound), transition probabilities $P(s'\mid s,a)$, a discount factor $\gamma\in(0,1)$ and an initial distribution $\rho$ on $\mathcal S$. $\Pi$ is the set of stationary randomized policies $\pi:\mathcal S\to\Delta(\mathcal A)$, $V_\pi$ the value function of $\pi$, $Q_\pi(s,a)=r(s,a)+\gamma\sum_{s'}P(s'\mid s,a)V_\pi(s')$, $V^*(s)=\max_{\pi\in\Pi}V_\pi(s)$, $J(\pi)=(1-\gamma)\sum_s\rho(s)V_\pi(s)$ and $\eta_\pi=(1-\gamma)\sum_{t\ge0}\gamma^t\rho P_\pi^t$ the discounted state occupancy measure.
--
--   A state aggregation $\phi$ partitions $\mathcal S$ into segments $\mathcal S_i=\phi^{-1}(i)$; $\Pi_\phi=\{\pi\in\Pi:\pi(s)=\pi(s')\text{ whenever }\phi(s)=\phi(s')\}$ is the state-aggregated policy class.
--
--   **Theorem 3 (Quality of stationary points).** Suppose $\rho(\phi^{-1}(i))>0$ for each segment $i$. If $\pi_\infty\in\Pi_\phi$ is a first order stationary point of $J(\cdot)$ on $\Pi_\phi$ (Definition 1), then for every optimal policy $\pi^*$ (that is, $V_{\pi^*}(s)=V^*(s)$ for every $s$),
--   $$J(\pi^*)-J(\pi_\infty)\le(1-\gamma)\|V_{\pi_\infty}-V^*\|_\infty\le2\epsilon_\phi,$$
--   where $\epsilon_\phi$ is the inherent state aggregation error of Definition 2; the bound holds with any $\varepsilon\ge\epsilon_\phi$ in its place.
--
--   Because $J$ is normalized to an average reward per period, the gap $J(\pi^*)-J(\pi_\infty)$ is the per-period regret of a limit point of policy gradient on the aggregated class. The bound does not depend on the effective horizon $1/(1-\gamma)$, in contrast with the $\kappa_\rho\epsilon_\phi/(1-\gamma)$ bound of Theorem 4 and with approximate policy iteration (Theorem 7). The stationary point may be randomized.
--
--   **Formalization Note** $\pi_\infty$ is a stacked vector; $\nabla J$ is the gradient of `Jext`. The norm on $\mathbb R^{\mathcal S}$ is the sup norm.
--
--   Differences from the source:
--   - correction: π∞ a stationary point of J on Πφ in the sense of Definition 1 (π∞ ∈ Π) → π∞ ∈ Πφ (hmem) and stationary in the sense of Definition 1; reason: with π∞ ∈ Π only the statement is false: 3 states x,y,z, one segment, actions α (reward 0), β (reward 1), deterministic moves x:α→x,β→z; y:α→z,β→x; z:α→x,β→z, γ=9/10, ρ=(1/50,1/2,12/25); ϵφ=0, π∞=(α,α,β) ∉ Πφ is stationary (directional derivatives −93/10, −1/5) with V_π∞=(0,9,10), V*=(10,10,10), J(π*)−J(π∞)=7/100>0; the proof (pp.10–11) uses π∞ ∈ Πφ
--   - generalization: ϵφ, the smallest scalar satisfying Definition 2's inequality → any ε with IsAggErrorBound (Definition 2's inequality); reason: ϵφ itself satisfies the inequality, so the statement specializes to the printed one
--   - generalization: φ : S → {1,…,m} with ρ(φ⁻¹(i)) > 0 for each i ∈ {1,…,m} → φ : S → ι with positive ρ-mass on the segment of every state; reason: for ι = Fin m the printed hypothesis implies this one (and forces φ onto); the labels play no other role
--   - encoding: ∇J(π) for J : Π → ℝ, policies stacked in ℝ^{|S|·|A|} → gradient of Jext = (1−γ)·directValue on EuclideanSpace ℝ (S × A); reason: Jext equals J on Π and is differentiable at every point of Π (Lemma 5), so its gradient is the paper's ∇J
--   - encoding: V*(s) = max_{π∈Π} V_π(s) → Vstar = sSup of {V_π(s) : π ∈ Π}; reason: the set is bounded and the maximum is attained (an optimal policy exists, p.4), so sSup is the maximum
--   - encoding: π* denotes some optimal policy (pp.4–5) → every policy πstar with V_πstar = V* (∀ πstar); reason: the paper says the choice among several optimal policies does not change the results (p.5); all of them have the same J
-- source:
--   Russo, Approximation Benefits of Policy Gradient Methods with Aggregated States, arXiv:2007.11684v3, Theorem 3, p.8 (proof pp.9–11)

import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_IsPolicy
import Definitions.Def_FoundationsML_ReinforcementLearning_IsTransitionKernel
import Definitions.Def_FoundationsML_ReinforcementLearning_PolicyValue
import Definitions.Def_PolicyGradTheory_ProjGA_MDP
import Definitions.Def_PolicyGradTheory_ProjGA_Algorithm
import Definitions.Def_AggStatePG_Vstar
import Definitions.Def_AggStatePG_objective
import Definitions.Def_AggStatePG_aggSet
import Definitions.Def_AggStatePG_IsFirstOrderStationary
import Definitions.Def_AggStatePG_IsAggErrorBound

open FoundationsML.ReinforcementLearning PolicyGradTheory.ProjGA

namespace AggStatePG

/-- **Theorem 3** (Quality of stationary points; Russo, *Approximation Benefits of Policy Gradient Methods with Aggregated States*, arXiv:2007.11684v3, Theorem 3, p.8), corrected: `π_∞ ∈ Π_φ`.
Suppose `ρ(φ^{-1}(i)) > 0` for each segment `i`. If `π_∞ ∈ Π_φ` is a stationary point of `J(·)` on
`Π_φ`, then
`J(π*) - J(π_∞) ≤ (1-γ) ‖V_{π_∞} - V*‖_∞ ≤ 2ϵ_φ`
for every optimal policy `π*` (`V_{π*}(s) = V*(s)` for every `s`).

**Formalization Note.**
* The MDP: finite `S`, `A`; `P s a s' = P(s'|s,a)` a transition kernel; `r : S → A → ℝ` arbitrary;
  `γ ∈ (0,1)`; `ρ` a distribution on `S`. `J = objective` ((2)), `V_π = PolicyValue`, `V* = Vstar`.
* The aggregation is any `φ : S → ι`; positivity is required for the segment of every state.
* `ε` is any bound with `IsAggErrorBound` (Definition 2's inequality); `ϵ_φ` is the least one.
* `π_∞` is a stacked vector (p.7) in `Π_φ = aggSet φ`, stationary in the sense of Definition 1
  (`IsFirstOrderStationary`, gradient of `Jext`). Definition 1 alone allows `π_∞ ∈ Π`; then the
  theorem is false (3 states, 1 segment, `ϵ_φ = 0`, `J(π*) - J(π_∞) = 7/100`), and the proof on
  pp.10–11 uses `π_∞ ∈ Π_φ`; hence the hypothesis `hmem`. `π_∞` may be randomized.
* `‖·‖` on `S → ℝ` is the sup norm `‖·‖_∞`. -/
theorem theorem_3 {S A ι : Type*} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq ι]
    (P : S → A → S → ℝ) (hP : IsTransitionKernel P) (r : S → A → ℝ)
    (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1) (ρ : S → ℝ) (hρ : IsDist ρ) (φ : S → ι)
    (hseg : ∀ s : S, 0 < ∑ s' ∈ Finset.univ.filter (fun s' => φ s' = φ s), ρ s')
    (ε : ℝ) (hε : IsAggErrorBound P r γ φ ε)
    (πinf : EuclideanSpace ℝ (S × A)) (hmem : πinf ∈ aggSet φ)
    (hstat : IsFirstOrderStationary P r γ ρ (aggSet φ) πinf) :
    (∀ πstar : S → A → ℝ, IsPolicy πstar → (∀ s : S, PolicyValue πstar P r γ s = Vstar P r γ s) →
      objective P r γ ρ πstar - objective P r γ ρ (asPolicy πinf) ≤
        (1 - γ) * ‖(fun s => PolicyValue (asPolicy πinf) P r γ s) - Vstar P r γ‖) ∧
    (1 - γ) * ‖(fun s => PolicyValue (asPolicy πinf) P r γ s) - Vstar P r γ‖ ≤ 2 * ε := by sorry

end AggStatePG
