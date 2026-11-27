-- Prove2me | Theorems.Thm_AggStatePG_Supplement_theorem_8
-- name    : AggStatePG.Supplement.theorem_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T03:25:33.22334+00:00
-- url     : https://prove2.me/theorems/9cc2d7dd-1b49-56a2-aa9b-1f722feb7985
-- title:
--   Theorem 8, p.16: Frank-Wolfe policy gradient and soft API with on-policy weights produce identical policies
-- statement:
--   Throughout, a finite Markov decision process $M=(\mathcal S,\mathcal A,r,P,\gamma,\rho)$ has finite state and action sets, real rewards $r(s,a)$, transition probabilities $P(s'\mid s,a)$, a discount factor $\gamma\in(0,1)$ and an initial distribution $\rho$. Policies $\pi\in\Pi$ are stacked vectors in $\mathbb R^{|\mathcal S|\cdot|\mathcal A|}$; $J(\pi)=(1-\gamma)\sum_s\rho(s)V_\pi(s)$ with gradient $\nabla J(\pi)$; $Q_\pi$ is the state-action value function and $\eta_\pi$ the discounted state occupancy measure from $\rho$. $\phi$ is a state aggregation with aggregated classes $\Pi_\phi$ and $\mathcal Q_\phi$.
--
--   **Theorem 8.** Run Algorithm 3 (Frank-Wolfe policy gradient) and Algorithm 4 (soft API with on-policy weights) with the same inputs: a step size $\alpha\in[0,1]$, an initial policy $\pi_1\in\Pi$ and the aggregation $\phi$. Suppose that the optimization problems in step (2) of Algorithm 3,
--   $$\max_{\pi\in\Pi_\phi}\langle\nabla J(\pi_t),\pi-\pi_t\rangle,$$
--   and in step (3) of Algorithm 4,
--   $$\max_{a\in\mathcal A}\hat Q_t(s,a)\quad(s\in\mathcal S),$$
--   always have unique solutions. Then the two algorithms produce identical sequences of policies: $\pi^{\mathrm{FW}}_t=\pi^{\mathrm{API}}_t$ for every $t\ge1$.
--
--   The equivalence connects policy gradient with approximate policy iteration: Frank-Wolfe policy gradient is API with two changes, on-policy state-relevance weights in the least-squares evaluation step and soft (incremental) policy updates. The initial policy need not be state-aggregated.
--
--   **Formalization Note** Uniqueness in Algorithm 3 is stated for the run of Algorithm 3, and uniqueness in Algorithm 4 for each state at every iteration of the run of Algorithm 4. Uniqueness of Algorithm 4's least-squares step is not assumed.
--
--   Differences from the source:
--   - reading: the step size α (an input of Algorithms 3 and 4, range unspecified) → α ∈ [0,1]; reason: the soft update is then a convex combination and every iterate is a policy, where ∇J, Q_π and η_π are the paper's objects
--   - encoding: π̃t+1 = argmax over Πφ in step (2) of Algorithm 3 → π̃t+1 is a maximizer, with uniqueness a hypothesis; reason: the theorem assumes the maximizer unique, so the two readings agree under it
--   - encoding: "always have unique solutions" → every maximizer of step (2) of Algorithm 3 equals π̃t+1, and argmax_a Q̂t(s,a) has at most one element, at every t ≥ 1 and every s; reason: the maximizers exist (π̃t+1 and the greedy action), so at most one solution is exactly one
--   - encoding: identical sequence of policies → x t = y t for every t ≥ 1 (stacked vectors); reason: iterations are indexed from t = 1 as on the page
-- source:
--   Russo, Approximation Benefits of Policy Gradient Methods with Aggregated States, arXiv:2007.11684v3, Theorem 8, p.16; Algorithms 3 and 4, p.17

import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_IsTransitionKernel
import Definitions.Def_PolicyGradTheory_ProjGA_MDP
import Definitions.Def_PolicyGradTheory_ProjGA_Algorithm
import Definitions.Def_AggStatePG_Jext
import Definitions.Def_AggStatePG_aggSet
import Definitions.Def_AggStatePG_Supplement_IsFWPGRun
import Definitions.Def_AggStatePG_Supplement_IsSoftAPIRun

open FoundationsML.ReinforcementLearning PolicyGradTheory.ProjGA

namespace AggStatePG.Supplement

/-- **Theorem 8** (Russo, *Approximation Benefits of Policy Gradient Methods with Aggregated
States*, arXiv:2007.11684v3, Theorem 8, p.16). Suppose Algorithms 3 and 4 are applied with the same
inputs and the optimization problems in step (2) of Algorithm 3 and step (3) of Algorithm 4 always
have unique solutions. Then each algorithm produces an identical sequence of policies.

**Formalization Note.**
* The MDP (p.4): finite `S`, `A`; `P` a transition kernel; real rewards `r`; `γ ∈ (0,1)`; `ρ` a
  distribution. The common inputs are `α`, `π_1 = x₁ ∈ Π` (`simplexSet`, not necessarily in `Π_φ`)
  and `φ : S → ι`.
* The step size `α` is not specified on p.17; it is read as `α ∈ [0,1]`, so that the soft update is
  a convex combination and every iterate is a policy (where `∇J`, `Q_π` and `η_π` are the paper's
  objects).
* `x, x̃` is any run of Algorithm 3 (`IsFWPGRun`) and `y, ỹ, Q̂` any run of Algorithm 4
  (`IsSoftAPIRun`), both from these inputs.
* Uniqueness in step (2) of Algorithm 3 (`huniq3`): at every `t ≥ 1`, every maximizer over `Π_φ` of
  `π ↦ ⟨∇J(x t), π − x t⟩` equals `x̃ (t+1)`. Uniqueness in step (3) of Algorithm 4 (`huniq4`): at
  every `t ≥ 1` and every state `s`, `argmax_a Q̂_t(s, a)` has at most one element. Uniqueness of
  Algorithm 4's least-squares step (2) is not assumed (the page does not assume it).
* "Identical sequence of policies": `x t = y t` for every `t ≥ 1`. -/
theorem theorem_8 {S A ι : Type*} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]
    (P : S → A → S → ℝ) (hP : IsTransitionKernel P) (r : S → A → ℝ)
    (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1) (ρ : S → ℝ) (hρ : IsDist ρ) (φ : S → ι)
    (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (x₁ : EuclideanSpace ℝ (S × A)) (hx₁ : x₁ ∈ simplexSet S A)
    (x xt y yt : ℕ → EuclideanSpace ℝ (S × A)) (Qhat : ℕ → S → A → ℝ)
    (hFW : IsFWPGRun P r γ ρ φ α x₁ x xt)
    (hSAPI : IsSoftAPIRun P r γ ρ φ α x₁ y yt Qhat)
    (huniq3 : ∀ t : ℕ, 1 ≤ t → ∀ z ∈ (AggStatePG.aggSet φ : Set (EuclideanSpace ℝ (S × A))),
      (∀ z' ∈ (AggStatePG.aggSet φ : Set (EuclideanSpace ℝ (S × A))),
        inner ℝ (gradient (AggStatePG.Jext P r γ ρ) (x t)) (z' - x t) ≤
          inner ℝ (gradient (AggStatePG.Jext P r γ ρ) (x t)) (z - x t)) →
      z = xt (t + 1))
    (huniq4 : ∀ t : ℕ, 1 ≤ t → ∀ (s : S) (a b : A),
      (∀ c : A, Qhat t s c ≤ Qhat t s a) → (∀ c : A, Qhat t s c ≤ Qhat t s b) → a = b) :
    ∀ t : ℕ, 1 ≤ t → x t = y t := by sorry

end AggStatePG.Supplement
