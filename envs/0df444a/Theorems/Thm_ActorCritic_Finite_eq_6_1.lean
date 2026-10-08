-- Prove2me | Theorems.Thm_ActorCritic_Finite_eq_6_1
-- name    : ActorCritic.Finite.eq_6_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T02:16:37.665497+00:00
-- url     : https://prove2.me/theorems/57b49354-63fa-44a8-a801-003fd8ab5346
-- title:
--   Eq. (6.1) — Taylor descent inequality for ᾱ(θ_{k+1}) along the actor update
-- statement:
--   Let a finite cost MDP and a policy family $\mu_\theta$ satisfy Assumption 2.1 (with data $N$, $x^*$, $\epsilon_0$). There is a constant $C$, reflecting a bound on the Hessian of $\bar\alpha$, such that for every choice of critic features $\phi_\theta$, step sizes, function $\Gamma$, critic (TD(1) or TD($\lambda$)), initial value, every path $((\hat X_k,\hat U_k))_k$ and every $k$, the iterates of the algorithm satisfy
--   $$
--   \bar\alpha(\theta_{k+1})\le\bar\alpha(\theta_k)-\beta_k\Gamma(\bar r(\theta_k))\nabla\bar\alpha(\theta_k)\cdot f(\theta_k)-\beta_k\nabla\bar\alpha(\theta_k)\cdot e^{(1)}_k-\beta_k\nabla\bar\alpha(\theta_k)\cdot e^{(2)}_k+C\beta_k^2\big|H_{\theta_k}(\hat X_{k+1},\hat U_{k+1})(r_k\Gamma(r_k))\big|^2 .
--   $$
--
--   This decomposes one actor step into a descent term along $f(\theta_k)\approx\nabla\bar\alpha(\theta_k)$, two noise terms and a second-order remainder; summing it over blocks of iterations is the proof of the main theorem.
--
--   **Formalization Note** The paper prints $\Gamma(\bar r(\theta))$ with a free $\theta$; it is read as $\Gamma(\bar r(\theta_k))$, the coefficient produced by the decomposition of the actor update on p. 1162. The inequality is deterministic and holds along every path.
-- source:
--   Konda and Tsitsiklis, On Actor-Critic Algorithms, SIAM J. Control Optim. 42 (2003), p. 1162, Eq. (6.1)

import Mathlib
import Definitions.Def_ActorCritic_Finite_SteadyState

namespace ActorCritic.Finite

/-- **Eq. (6.1)** (Konda–Tsitsiklis 2003, p. 1162), finite case, with the misprinted
`Γ(r̄(θ))` read as `Γ(r̄(θ_k))`. Under Assumption 2.1 (data `N`, `x*`, `ε₀`), there is a constant
`C` (reflecting a bound on the Hessian of `ᾱ`) such that for every critic, every choice of
features, step sizes and `Γ`, every initial value and every path `ω`, and every `k`,
`ᾱ(θ_{k+1}) ≤ ᾱ(θ_k) − β_k Γ(r̄(θ_k)) ∇ᾱ(θ_k)·f(θ_k) − β_k ∇ᾱ(θ_k)·e^{(1)}_k − β_k ∇ᾱ(θ_k)·e^{(2)}_k
  + C β_k² |H_{θ_k}(X̂_{k+1}, Û_{k+1})(r_k Γ(r_k))|²`. -/
theorem eq_6_1
    {X U : Type} [Fintype X] [Fintype U] [DecidableEq X] [DecidableEq U]
    {n : ℕ} (M : FiniteMDP X U) (π : RSPFamily X U n)
    (N : ℕ) (xstar : X) (ε₀ : ℝ)
    (h21a : Assumption21a π) (h21b : Assumption21b π) (h21c : Assumption21c M π)
    (h21d : Assumption21d M π N xstar ε₀) :
    ∃ C : ℝ, ∀ (m : ℕ) (φ : Feat X U n m) (β γ : ℕ → ℝ) (Γ : EuclideanSpace ℝ (Fin m) → ℝ)
      (crit : Critic X) (s₀ : ACState n m) (ω : ℕ → X × U) (k : ℕ),
      let s := acIter M π φ β γ Γ crit s₀ ω k
      let s' := acIter M π φ β γ Γ crit s₀ ω (k + 1)
      let g := gradient (avgCost M π) s.θ
      avgCost M π s'.θ ≤ avgCost M π s.θ
        - β k * Γ (rbar M π φ crit s.θ) * inner ℝ g (fvec M π φ crit s.θ)
        - β k * inner ℝ g (noise1 M π φ β γ Γ crit s₀ ω k)
        - β k * inner ℝ g (noise2 M π φ β γ Γ crit s₀ ω k)
        + C * β k ^ 2 *
          ‖(WithLp.toLp 2 ((Hmat π φ s.θ (ω (k + 1))).mulVec (fun j => Γ s.r * s.r j)) :
            EuclideanSpace ℝ (Fin n))‖ ^ 2 := by sorry

end ActorCritic.Finite
