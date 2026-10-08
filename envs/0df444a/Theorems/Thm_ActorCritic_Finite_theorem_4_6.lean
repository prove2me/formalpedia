-- Prove2me | Theorems.Thm_ActorCritic_Finite_theorem_4_6
-- name    : ActorCritic.Finite.theorem_4_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T02:14:22.440555+00:00
-- url     : https://prove2.me/theorems/4d0865ff-780b-4bb6-84f3-9ef5bd0f657a
-- title:
--   Theorem 4.6 — ∇ᾱ(θ) = ⟨ψ_θ, Q_θ⟩_θ for every Poisson solution, and ∇ᾱ has bounded derivatives
-- statement:
--   Let $(\mathbb X,\mathbb U,p,c)$ be a finite cost MDP and $\mu_\theta$ a family of randomized stationary policies satisfying Assumption 2.1 (with data $N$, $x^*$, $\epsilon_0$). Then the average cost $\bar\alpha(\theta)=\sum_{x,u}c(x,u)\eta_\theta(x,u)$ is differentiable, and for every $\theta\in\mathbb R^n$ and every solution $Q$ of the Poisson equation $Q=c-\bar\alpha(\theta)\underline1+P_\theta Q$,
--   $$
--   \nabla\bar\alpha(\theta)=\langle\psi_\theta,Q\rangle_\theta=\sum_{x,u}\eta_\theta(x,u)\,Q(x,u)\,\psi_\theta(x,u).
--   $$
--   Furthermore $\nabla\bar\alpha$ is differentiable and its derivative (the Hessian of $\bar\alpha$) is bounded uniformly in $\theta$.
--
--   The gradient formula is the basis of the actor update, and the Hessian bound gives the Taylor inequality (6.1) used in the convergence proof of the actor.
--
--   **Formalization Note** The paper states the theorem for Polish spaces under its Assumptions 4.1, 4.2, 4.4 and 4.5; in the finite case these follow from Assumption 2.1 (pp. 1150, 1152), which is the hypothesis here. "Bounded derivatives" is read as a bound uniform in $\theta$, as (6.1) uses it. In the finite case the gradient formula is also the paper's Theorem 2.2, recalled from [16].
-- source:
--   Konda and Tsitsiklis, On Actor-Critic Algorithms, SIAM J. Control Optim. 42 (2003), p. 1153, Theorem 4.6 (Poisson equation (4.4), p. 1152)

import Mathlib
import Definitions.Def_ActorCritic_Finite_Model

namespace ActorCritic.Finite

/-- **Theorem 4.6** (Konda–Tsitsiklis 2003, p. 1153), finite case. Under Assumption 2.1 (which,
in the finite case, yields the paper's Assumptions 4.1, 4.2, 4.4 and 4.5): the average cost
`ᾱ` is differentiable; for every `θ` and **every** solution `Q` of the Poisson equation (4.4) with
parameter `θ`, `∇ᾱ(θ) = ⟨ψ_θ, Q⟩_θ = ∑_{x,u} η_θ(x, u) Q(x, u) ψ_θ(x, u)`; and `∇ᾱ` is
differentiable with a derivative (the Hessian of `ᾱ`) bounded uniformly in `θ`. -/
theorem theorem_4_6
    {X U : Type} [Fintype X] [Fintype U] [DecidableEq X] [DecidableEq U]
    {n : ℕ} (M : FiniteMDP X U) (π : RSPFamily X U n)
    (N : ℕ) (xstar : X) (ε₀ : ℝ)
    (h21a : Assumption21a π) (h21b : Assumption21b π) (h21c : Assumption21c M π)
    (h21d : Assumption21d M π N xstar ε₀) :
    Differentiable ℝ (avgCost M π) ∧
    (∀ (θ : EuclideanSpace ℝ (Fin n)) (Q : X × U → ℝ), IsPoissonSol M π θ Q →
      gradient (avgCost M π) θ = ∑ x, ∑ u, (eta M π θ x u * Q (x, u)) • score π θ x u) ∧
    Differentiable ℝ (gradient (avgCost M π)) ∧
    ∃ C : ℝ, ∀ θ, ‖fderiv ℝ (gradient (avgCost M π)) θ‖ ≤ C := by sorry

end ActorCritic.Finite
