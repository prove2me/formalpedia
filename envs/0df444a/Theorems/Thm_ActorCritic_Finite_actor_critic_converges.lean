-- Prove2me | Theorems.Thm_ActorCritic_Finite_actor_critic_converges
-- name    : ActorCritic.Finite.actor_critic_converges
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T02:17:08.148889+00:00
-- url     : https://prove2.me/theorems/f81d250d-977d-4091-85e8-87a96c26b872
-- title:
--   Theorem 3.4 — actor–critic with TD(1) critic: liminf_k |∇ᾱ(θ_k)| = 0 w.p.1; with TD(λ), λ near 1: liminf_k |∇ᾱ(θ_k)| < ε w.p.1
-- statement:
--   Let $(\mathbb X,\mathbb U,p,c)$ be a finite cost MDP, $\mu_\theta$ ($\theta\in\mathbb R^n$) a family of randomized stationary policies, $\phi_\theta(x,u)\in\mathbb R^m$ critic features, $\beta_k,\gamma_k$ step sizes and $\Gamma:\mathbb R^m\to\mathbb R$, and suppose Assumptions 2.1 (with data $N$, $x^*$, $\epsilon_0$), 3.1, 3.2 and 3.3 hold. Write $\theta_k$ for the actor iterates of the actor–critic algorithm (3.1)–(3.2) and $\bar\alpha(\theta)$ for the average cost. Then $\bar\alpha$ is differentiable, and:
--
--   1. **(TD(1) critic.)** If, in addition, Assumption 4.9 holds at $x^*$, then for the algorithm with the TD(1) critic resetting at $x^*$, for every deterministic initial value $(\theta_0,r_0,\alpha_0,\hat Z_0)$ and every initial law of $(\hat X_0,\hat U_0)$,
--   $$
--   \liminf_{k\to\infty}|\nabla\bar\alpha(\theta_k)|=0\quad\text{with probability }1.
--   $$
--   2. **(TD($\lambda$) critic.)** For every $\epsilon>0$ there is $\bar\lambda\in(0,1)$ such that for every $\lambda\in[\bar\lambda,1)$, for the algorithm with the TD($\lambda$) critic, every deterministic initial value and every initial law,
--   $$
--   \liminf_{k\to\infty}|\nabla\bar\alpha(\theta_k)|<\epsilon\quad\text{with probability }1.
--   $$
--
--   This is the main result of the paper: actor–critic methods whose critic uses linear function approximation with features spanning the score functions drive the policy gradient to zero along a subsequence (TD(1)) or to an arbitrarily small neighbourhood of zero (TD($\lambda$) with $\lambda$ close to $1$).
--
--   **Formalization Note** Three readings are pinned. (i) Theorem 3.4 does not list Assumption 4.9, but its TD(1) analysis uses it (p. 1157) and Theorem 6.3, of which Theorem 3.4 is the finite case, assumes it; it is added to part 1 only, because the TD($\lambda$) analysis of §5.2 does not use it. (ii) "$\lambda$ sufficiently close to $1$" is read as: there is $\bar\lambda<1$ such that every $\lambda\in[\bar\lambda,1)$ works; $\bar\lambda$ is chosen after the model, features, step sizes and $\Gamma$ and before the initial conditions and the path. (iii) The paper fixes no initial conditions; the statement holds for all deterministic $(\theta_0,r_0,\alpha_0,\hat Z_0)$ and all initial laws. Assumption 3.3(b) is in its corrected reading (see the definitions module). The $\liminf$ is taken in $[0,\infty]$, so that a sequence $|\nabla\bar\alpha(\theta_k)|\to\infty$ has $\liminf=\infty$ rather than a junk real value. Differentiability of $\bar\alpha$ is stated because Lean's `gradient` is $0$ at points of non-differentiability. "With probability $1$" is with respect to the law of the simulated path defined in the algorithm module.
-- source:
--   Konda and Tsitsiklis, On Actor-Critic Algorithms, SIAM J. Control Optim. 42 (2003), p. 1149, Theorem 3.4 (general form: p. 1163, Theorem 6.3; Assumption 4.9, p. 1155)

import Mathlib
import Definitions.Def_ActorCritic_Finite_SteadyState

open MeasureTheory ProbabilityTheory Filter

namespace ActorCritic.Finite

/-- **Theorem 3.4** (Konda–Tsitsiklis 2003, p. 1149), finite state and action spaces.
Under Assumptions 2.1 (with data `N`, `x*`, `ε₀`), 3.1, 3.2 and 3.3 (with (3.3) in its corrected
reading, see `Assumption33b`):
* the average cost `ᾱ` is differentiable (presupposed by the paper, which writes `∇ᾱ`);
* (a) with a TD(1) critic resetting at `x*`, and under Assumption 4.9 at `x*` (used by the proof,
  not listed in the printed theorem), for every initial value `(θ_0, r_0, α_0, Ẑ_0)` and every
  initial law `ν₀` of `(X̂_0, Û_0)`, almost surely `liminf_k |∇ᾱ(θ_k)| = 0`;
* (b) for every `ε > 0` there is `λ̄ ∈ (0, 1)` such that for every `λ ∈ [λ̄, 1)`, with a TD(λ)
  critic, for every initial value and initial law, almost surely `liminf_k |∇ᾱ(θ_k)| < ε`.
The `liminf` is taken in `ℝ≥0∞`, so a sequence `|∇ᾱ(θ_k)| → ∞` has `liminf = ∞`. -/
theorem actor_critic_converges
    {X U : Type} [Fintype X] [Fintype U] [DecidableEq X] [DecidableEq U]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    [MeasurableSpace U] [MeasurableSingletonClass U]
    {n m : ℕ} (M : FiniteMDP X U) (π : RSPFamily X U n) (φ : Feat X U n m)
    (β γ : ℕ → ℝ) (Γ : EuclideanSpace ℝ (Fin m) → ℝ)
    (N : ℕ) (xstar : X) (ε₀ : ℝ)
    (h21a : Assumption21a π) (h21b : Assumption21b π) (h21c : Assumption21c M π)
    (h21d : Assumption21d M π N xstar ε₀)
    (h31 : Assumption31 π φ) (h32 : Assumption32 M π φ)
    (h33a : Assumption33a β γ) (h33b : Assumption33b Γ) :
    Differentiable ℝ (avgCost M π) ∧
    (Assumption49 π φ xstar →
      ∀ (s₀ : ACState n m) (ν₀ : Measure (X × U)) [IsProbabilityMeasure ν₀],
        ∀ᵐ ω ∂(pathLaw M π φ β γ Γ (Critic.td1 xstar) s₀ ν₀),
          liminf (fun k => ENNReal.ofReal
            ‖gradient (avgCost M π) (acIter M π φ β γ Γ (Critic.td1 xstar) s₀ ω k).θ‖)
            atTop = 0) ∧
    (∀ ε : ℝ, 0 < ε → ∃ lamBar : ℝ, 0 < lamBar ∧ lamBar < 1 ∧
      ∀ lam : ℝ, lamBar ≤ lam → lam < 1 →
        ∀ (s₀ : ACState n m) (ν₀ : Measure (X × U)) [IsProbabilityMeasure ν₀],
          ∀ᵐ ω ∂(pathLaw M π φ β γ Γ (Critic.tdLambda lam) s₀ ν₀),
            liminf (fun k => ENNReal.ofReal
              ‖gradient (avgCost M π) (acIter M π φ β γ Γ (Critic.tdLambda lam) s₀ ω k).θ‖)
              atTop < ENNReal.ofReal ε) := by sorry

end ActorCritic.Finite
