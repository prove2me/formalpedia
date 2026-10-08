-- Prove2me | Theorems.Thm_ActorCritic_Finite_lemma_6_1
-- name    : ActorCritic.Finite.lemma_6_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T02:16:38.627059+00:00
-- url     : https://prove2.me/theorems/03e616ef-251d-4856-bfb3-40862964028f
-- title:
--   Lemma 6.1 — f(θ) = ∇ᾱ(θ) + ε(λ, θ) with sup_θ |ε(λ, θ)| ≤ C(1 − λ), C independent of λ
-- statement:
--   Let a finite cost MDP, a policy family $\mu_\theta$ and critic features $\phi_\theta$ satisfy Assumptions 2.1 (with data $N$, $x^*$, $\epsilon_0$), 3.1 and 3.2. For a TD($\lambda$) critic with $0<\lambda\le1$ (the case $\lambda=1$ being the TD(1) critic resetting at $x^*$), let $\bar r(\theta)$ solve $\bar G_1(\theta)\bar r(\theta)=\bar h_1(\theta)$ and $f(\theta)=\bar H(\theta)\bar r(\theta)$ with $\bar H(\theta)=\langle\psi_\theta,\phi_\theta'\rangle_\theta$. Then there is a constant $C>0$, independent of $\lambda$, such that
--   $$
--   \sup_\theta\big|f(\theta)-\nabla\bar\alpha(\theta)\big|\le C(1-\lambda)\qquad\text{for all }\lambda\in(0,1],
--   $$
--   and in particular $f(\theta)=\nabla\bar\alpha(\theta)$ for the TD(1) critic.
--
--   The vector $f(\theta)$ is the mean direction of the actor update once the critic has converged; the lemma says it is the true gradient up to an error controlled by $1-\lambda$, which is why $\lambda$ close to $1$ gives an approximately stationary point in Theorem 3.4(b).
--
--   **Formalization Note** The paper writes $f(\theta)=\nabla\bar\alpha(\theta)+\varepsilon(\lambda,\theta)$ with $\sup_\theta|\varepsilon(\lambda,\theta)|\le C(1-\lambda)$; since $\varepsilon$ is defined by that equation, the bound is stated directly on $f-\nabla\bar\alpha$. One constant $C$ serves all $\lambda\in(0,1)$ and all $\theta$; at $\lambda=1$ the bound is the identity. Lean's `gradient` is $0$ where $\bar\alpha$ is not differentiable; under 2.1 it is differentiable (Theorem 4.6).
-- source:
--   Konda and Tsitsiklis, On Actor-Critic Algorithms, SIAM J. Control Optim. 42 (2003), p. 1162, Lemma 6.1 (H_θ, H̄, r̄, f on p. 1162)

import Mathlib
import Definitions.Def_ActorCritic_Finite_SteadyState

namespace ActorCritic.Finite

/-- **Lemma 6.1** (Konda–Tsitsiklis 2003, p. 1162), finite case. Under Assumptions 2.1 (data `N`,
`x*`, `ε₀`), 3.1 and 3.2, write `f(θ) = H̄(θ) r̄(θ)` with `r̄(θ)` the solution of
`Ḡ₁(θ) r̄(θ) = h̄₁(θ)` for the critic in use. There is a constant `C > 0`, independent of `λ`,
such that for the TD(λ) critic with `0 < λ ≤ 1` (`λ = 1` being the TD(1) critic resetting at
`x*`), `sup_θ |f(θ) − ∇ᾱ(θ)| ≤ C (1 − λ)`. At `λ = 1` this is the identity `f = ∇ᾱ`. -/
theorem lemma_6_1
    {X U : Type} [Fintype X] [Fintype U] [DecidableEq X] [DecidableEq U]
    {n m : ℕ} (M : FiniteMDP X U) (π : RSPFamily X U n) (φ : Feat X U n m)
    (N : ℕ) (xstar : X) (ε₀ : ℝ)
    (h21a : Assumption21a π) (h21b : Assumption21b π) (h21c : Assumption21c M π)
    (h21d : Assumption21d M π N xstar ε₀)
    (h31 : Assumption31 π φ) (h32 : Assumption32 M π φ) :
    ∃ C : ℝ, 0 < C ∧
      (∀ θ : EuclideanSpace ℝ (Fin n),
        fvec M π φ (Critic.td1 xstar) θ = gradient (avgCost M π) θ) ∧
      ∀ lam : ℝ, 0 < lam → lam < 1 → ∀ θ : EuclideanSpace ℝ (Fin n),
        ‖fvec M π φ (Critic.tdLambda lam) θ - gradient (avgCost M π) θ‖ ≤ C * (1 - lam) := by sorry

end ActorCritic.Finite
