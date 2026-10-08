-- Prove2me | Theorems.Thm_ActorCritic_Finite_theorem_5_7
-- name    : ActorCritic.Finite.theorem_5_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T02:16:31.728231+00:00
-- url     : https://prove2.me/theorems/200994e7-6c5a-431a-a011-7e4e9197f707
-- title:
--   Theorem 5.7 — the critic tracks: R_k is bounded and |Ḡ(θ_k)R_k − h̄(θ_k)| → 0 w.p.1
-- statement:
--   Consider the actor–critic algorithm on a finite cost MDP whose policy family, features, step sizes and $\Gamma$ satisfy Assumptions 2.1 (with data $N$, $x^*$, $\epsilon_0$), 3.1, 3.2 and 3.3, with either
--   1. the TD(1) critic resetting at $x^*$, together with Assumption 4.9 at $x^*$, or
--   2. the TD($\lambda$) critic with $0<\lambda<1$.
--
--   Then for every $L>0$, every deterministic initial value $(\theta_0,r_0,\alpha_0,\hat Z_0)$ and every initial law of $(\hat X_0,\hat U_0)$, with probability one the sequence $R_k=(L\alpha_k,r_k)$ is bounded and
--   $$
--   \lim_{k\to\infty}\big|\bar G(\theta_k)R_k-\bar h(\theta_k)\big|=0 .
--   $$
--
--   Equivalently, $\alpha_k-\bar\alpha(\theta_k)\to0$ and $\bar G_1(\theta_k)r_k-\bar h_1(\theta_k)\to0$: although the actor keeps moving, the critic follows the target $\bar r(\theta_k)$ it would converge to if the policy were frozen.
--
--   **Formalization Note** The printed theorem omits "w.p.1"; it is meant (the theorem is an instance of the almost-sure Theorem A.7, and boundedness is per path). The Polish-space assumptions it cites reduce to the finite ones: 4.1 ⊂ 2.1(c), 4.2 ⇐ 2.1(d), 4.4–4.5 ⇐ 2.1, 4.8(a)–(b) ⇐ 3.1(a), 4.8(c) = 3.2, 4.8(d) = 3.1(b). Assumption 4.9 is used for the TD(1) critic only. The conclusion does not depend on which $L>0$ is used. Norms on `Fin 1 ⊕ Fin m → ℝ` are sup norms, equivalent to the Euclidean norm for boundedness and convergence to $0$. The actor iterates $\theta_k$ are not assumed bounded.
-- source:
--   Konda and Tsitsiklis, On Actor-Critic Algorithms, SIAM J. Control Optim. 42 (2003), p. 1162, Theorem 5.7

import Mathlib
import Definitions.Def_ActorCritic_Finite_SteadyState

open MeasureTheory ProbabilityTheory Filter Topology

namespace ActorCritic.Finite

/-- **Theorem 5.7** (Konda–Tsitsiklis 2003, p. 1162), finite case. Under Assumptions 2.1 (data
`N`, `x*`, `ε₀`), 3.1, 3.2 and 3.3 (corrected (3.3)), and for either TD critic — TD(1) resetting
at `x*` together with Assumption 4.9 at `x*`, or TD(λ) with `0 < λ < 1` — for every `L > 0`,
every initial value `(θ_0, r_0, α_0, Ẑ_0)` and every initial law `ν₀`, almost surely the
sequence `R_k = (L α_k, r_k)` is bounded and `lim_k |Ḡ(θ_k) R_k − h̄(θ_k)| = 0`. -/
theorem theorem_5_7
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
    (crit : Critic X)
    (hcrit : (crit = Critic.td1 xstar ∧ Assumption49 π φ xstar) ∨
      ∃ lam : ℝ, 0 < lam ∧ lam < 1 ∧ crit = Critic.tdLambda lam)
    (L : ℝ) (hL : 0 < L) (s₀ : ACState n m) (ν₀ : Measure (X × U)) [IsProbabilityMeasure ν₀] :
    ∀ᵐ ω ∂(pathLaw M π φ β γ Γ crit s₀ ν₀),
      (∃ B : ℝ, ∀ k, ‖Rvec L (acIter M π φ β γ Γ crit s₀ ω k)‖ ≤ B) ∧
      Tendsto (fun k =>
        ‖(Gbar M π φ crit L (acIter M π φ β γ Γ crit s₀ ω k).θ).mulVec
            (Rvec L (acIter M π φ β γ Γ crit s₀ ω k)) -
          hbar M π φ crit L (acIter M π φ β γ Γ crit s₀ ω k).θ‖) atTop (𝓝 0) := by sorry

end ActorCritic.Finite
