-- Prove2me | Theorems.Thm_AggStatePG_lemma_5
-- name    : AggStatePG.lemma_5
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T12:43:44.439976+00:00
-- url     : https://prove2.me/theorems/daa3a445-383b-40d3-b466-3f9955faa32b
-- title:
--   Lemma 5, p.10: policy gradient theorem for directional derivatives
-- statement:
--   Throughout, $M=(\mathcal S,\mathcal A,r,P,\gamma,\rho)$ is a finite Markov decision process: finite state and action sets, a real reward $r(s,a)$ (no bound), transition probabilities $P(s'\mid s,a)$, a discount factor $\gamma\in(0,1)$ and an initial distribution $\rho$ on $\mathcal S$. $\Pi$ is the set of stationary randomized policies $\pi:\mathcal S\to\Delta(\mathcal A)$, $V_\pi$ the value function of $\pi$, $Q_\pi(s,a)=r(s,a)+\gamma\sum_{s'}P(s'\mid s,a)V_\pi(s')$, $V^*(s)=\max_{\pi\in\Pi}V_\pi(s)$, $J(\pi)=(1-\gamma)\sum_s\rho(s)V_\pi(s)$ and $\eta_\pi=(1-\gamma)\sum_{t\ge0}\gamma^t\rho P_\pi^t$ the discounted state occupancy measure.
--
--   For each $\pi,\pi'\in\Pi$ (viewed as stacked vectors in $\mathbb R^{|\mathcal S|\cdot|\mathcal A|}$), $J$ is differentiable at $\pi$ and
--   $$\langle\nabla J(\pi),\pi'-\pi\rangle=\sum_{s\in\mathcal S}\sum_{a\in\mathcal A}\eta_\pi(s)Q_\pi(s,a)\big(\pi'(s,a)-\pi(s,a)\big)=\langle Q_\pi,\pi'-\pi\rangle_{\eta_\pi\times1}.\qquad(7)$$
--
--   The directional derivative of the objective toward $\pi'$ is the average, over states drawn from the occupancy measure of $\pi$, of the one-period benefit of switching to $\pi'$. It is the first step of Lemma 6.
--
--   **Formalization Note** $J$ on vectors is `Jext` $=(1-\gamma)\cdot$`directValue` and $\nabla J$ is Mathlib's `gradient`; $\langle\cdot,\cdot\rangle_{w\times1}$ is `wInner` (6).
--
--   Differences from the source:
--   - generalization: (7), an identity for ∇J(π) → (7) together with the conclusion that J is differentiable at π; reason: makes ∇J(π) the true gradient rather than Lean's default value; dropping the clause gives (7)
--   - encoding: ∇J(π) for J : Π → ℝ, policies stacked in ℝ^{|S|·|A|} → gradient of Jext = (1−γ)·directValue on EuclideanSpace ℝ (S × A); reason: Jext equals J on Π and is differentiable at every point of Π (Lemma 5), so its gradient is the paper's ∇J
-- source:
--   Russo, Approximation Benefits of Policy Gradient Methods with Aggregated States, arXiv:2007.11684v3, Lemma 5, display (7), p.10

import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_IsTransitionKernel
import Definitions.Def_FoundationsML_ReinforcementLearning_QFunction
import Definitions.Def_PolicyGradTheory_ProjGA_MDP
import Definitions.Def_PolicyGradTheory_ProjGA_Algorithm
import Definitions.Def_AggStatePG_Jext
import Definitions.Def_AggStatePG_wInner

open FoundationsML.ReinforcementLearning PolicyGradTheory.ProjGA

namespace AggStatePG

/-- **Lemma 5** (Policy gradient theorem for directional derivatives; Russo, *Approximation Benefits of Policy Gradient Methods with Aggregated States*, arXiv:2007.11684v3, Lemma 5, p.10). For
each `π, π' ∈ Π`,
`⟨∇J(π), π' - π⟩ = ∑_{s ∈ S} ∑_{a ∈ A} η_π(s) Q_π(s,a) (π'(s,a) - π(s,a)) = ⟨Q_π, π' - π⟩_{η_π × 1}`. (7)

The statement has three parts: `J` is differentiable at `π` (so `∇J(π)` is its gradient), and the
two equalities of (7).

**Formalization Note.** Policies are stacked vectors `x, x' ∈ simplexSet S A` (p.7); `J` on vectors is
`Jext = (1-γ)·directValue` and `∇J` is Mathlib's `gradient`; `η_π = visitation`, `Q_π = QFunction`,
`⟨·,·⟩_{w×1} = wInner` (6). Rewards are arbitrary reals. -/
theorem lemma_5 {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]
    (P : S → A → S → ℝ) (hP : IsTransitionKernel P) (r : S → A → ℝ)
    (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1) (ρ : S → ℝ) (hρ : IsDist ρ)
    (x x' : EuclideanSpace ℝ (S × A)) (hx : x ∈ simplexSet S A) (hx' : x' ∈ simplexSet S A) :
    DifferentiableAt ℝ (Jext P r γ ρ) x ∧
    inner ℝ (gradient (Jext P r γ ρ) x) (x' - x) =
      ∑ s : S, ∑ a : A, visitation (asPolicy x) P γ ρ s * QFunction (asPolicy x) P r γ s a *
        (x' (s, a) - x (s, a)) ∧
    ∑ s : S, ∑ a : A, visitation (asPolicy x) P γ ρ s * QFunction (asPolicy x) P r γ s a *
        (x' (s, a) - x (s, a)) =
      wInner (visitation (asPolicy x) P γ ρ) (QFunction (asPolicy x) P r γ)
        (fun s a => x' (s, a) - x (s, a)) := by sorry

end AggStatePG
