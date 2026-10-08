-- Prove2me | Theorems.Thm_ActorCritic_Finite_lemma_5_2
-- name    : ActorCritic.Finite.lemma_5_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T02:16:41.542332+00:00
-- url     : https://prove2.me/theorems/a6916de8-63b8-46c5-ab23-50cc5af67211
-- title:
--   Lemma 5.2 — TD(1): sup_k E[|Ẑ_k|^d] < ∞ for every d > 1
-- statement:
--   Consider the actor–critic algorithm with a TD(1) critic resetting at $x^*$, on a finite cost MDP whose policy family, features, step sizes and $\Gamma$ satisfy Assumptions 2.1 (with data $N$, $x^*$, $\epsilon_0$), 3.1, 3.2 and 3.3. For every deterministic initial value $(\theta_0,r_0,\alpha_0,\hat Z_0)$, every initial law $\nu_0$ of $(\hat X_0,\hat U_0)$ and every $d>1$,
--   $$
--   \sup_k\mathbf E\big[|\hat Z_k|^d\big]<\infty ,
--   $$
--   the expectation being under the law of the simulated path.
--
--   The moment bound on the eligibility trace is one of the hypotheses of the stochastic-approximation result (Theorem A.7) from which the critic's tracking property (Theorem 5.7) follows.
--
--   **Formalization Note** $\mathbf E[|\hat Z_k|^d]$ is the lower Lebesgue integral of the nonnegative function $|\hat Z_k|^d$ (with values in $[0,\infty]$), so no integrability is presupposed and the bound is a genuine finiteness statement. Assumption 4.9, standing in §5.1, is not used by this lemma and is not assumed.
-- source:
--   Konda and Tsitsiklis, On Actor-Critic Algorithms, SIAM J. Control Optim. 42 (2003), p. 1158, Lemma 5.2

import Mathlib
import Definitions.Def_ActorCritic_Finite_SteadyState

open MeasureTheory ProbabilityTheory

namespace ActorCritic.Finite

/-- **Lemma 5.2** (Konda–Tsitsiklis 2003, p. 1158), TD(1) critic resetting at `x*`, finite case.
Under Assumptions 2.1 (data `N`, `x*`, `ε₀`), 3.1, 3.2 and 3.3 (corrected (3.3)), for every initial
value `(θ_0, r_0, α_0, Ẑ_0)` and every initial law `ν₀` of the algorithm, and every `d > 1`,
`sup_k E[|Ẑ_k|^d] < ∞`. The expectation is the lower Lebesgue integral of the nonnegative
function `|Ẑ_k|^d` under the law of the simulated path, so no integrability is presupposed. -/
theorem lemma_5_2
    {X U : Type} [Fintype X] [Fintype U] [DecidableEq X] [DecidableEq U]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    [MeasurableSpace U] [MeasurableSingletonClass U]
    {n m : ℕ} (M : FiniteMDP X U) (π : RSPFamily X U n) (φ : Feat X U n m)
    (β γ : ℕ → ℝ) (Γ : EuclideanSpace ℝ (Fin m) → ℝ)
    (N : ℕ) (xstar : X) (ε₀ : ℝ)
    (h21a : Assumption21a π) (h21b : Assumption21b π) (h21c : Assumption21c M π)
    (h21d : Assumption21d M π N xstar ε₀)
    (h31 : Assumption31 π φ) (h32 : Assumption32 M π φ)
    (h33a : Assumption33a β γ) (h33b : Assumption33b Γ)
    (s₀ : ACState n m) (ν₀ : Measure (X × U)) [IsProbabilityMeasure ν₀] :
    ∀ d : ℝ, 1 < d → ∃ B : ℝ, ∀ k : ℕ,
      ∫⁻ ω, ENNReal.ofReal
          (‖(acIter M π φ β γ Γ (Critic.td1 xstar) s₀ ω k).Z‖ ^ d)
        ∂(pathLaw M π φ β γ Γ (Critic.td1 xstar) s₀ ν₀) ≤ ENNReal.ofReal B := by sorry

end ActorCritic.Finite
