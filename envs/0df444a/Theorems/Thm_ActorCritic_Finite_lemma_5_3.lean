-- Prove2me | Theorems.Thm_ActorCritic_Finite_lemma_5_3
-- name    : ActorCritic.Finite.lemma_5_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T02:16:33.06918+00:00
-- url     : https://prove2.me/theorems/ef97b8a8-4d9a-4925-9ca6-28fb25280eb0
-- title:
--   Lemma 5.3 — TD(1): R'Ḡ(θ)R ≥ ε|R|² uniformly in θ, for some L and ε > 0
-- statement:
--   Let a finite cost MDP, a policy family $\mu_\theta$ and critic features $\phi_\theta$ satisfy Assumptions 2.1 (with data $N$, $x^*$, $\epsilon_0$), 3.1 and 3.2. For the TD(1) critic resetting at $x^*$ let
--   $$
--   \bar G(\theta)=\begin{pmatrix}1&0\\ \bar Z(\theta)/L&\bar G_1(\theta)\end{pmatrix},\qquad \bar Z(\theta)=\langle T_\theta,\phi_\theta\rangle_\theta,\quad \bar G_1(\theta)=\langle\phi_\theta,\phi_\theta'\rangle_\theta .
--   $$
--   Then there exist $L>0$ and $\epsilon>0$ such that for all $\theta\in\mathbb R^n$ and $R\in\mathbb R^{m+1}$,
--   $$
--   R'\bar G(\theta)R\ge\epsilon|R|^2 .
--   $$
--
--   This uniform positive definiteness is the stability hypothesis (Assumption A.6) under which the TD(1) critic tracks its moving target.
--
--   **Formalization Note** $R$ is indexed by `Fin 1 ⊕ Fin m` and $|R|^2=\sum_iR_i^2$. $T_\theta$ is the expected return time to $x^*$ of Lemma 5.1. The constant $L$ is required positive, as on p. 1156.
-- source:
--   Konda and Tsitsiklis, On Actor-Critic Algorithms, SIAM J. Control Optim. 42 (2003), p. 1159, Lemma 5.3 (Ḡ(θ), p. 1157; Z̄, Ḡ₁, p. 1158)

import Mathlib
import Definitions.Def_ActorCritic_Finite_SteadyState

namespace ActorCritic.Finite

/-- **Lemma 5.3** (Konda–Tsitsiklis 2003, p. 1159), TD(1) critic resetting at `x*`, finite case.
Under Assumptions 2.1 (data `N`, `x*`, `ε₀`), 3.1 and 3.2, there exist `L > 0` and `ε > 0` such
that for all `θ ∈ ℝⁿ` and `R ∈ ℝ^{1+m}`, `R' Ḡ(θ) R ≥ ε |R|²`, where
`Ḡ(θ) = [[1, 0], [Z̄(θ)/L, Ḡ₁(θ)]]` with `Z̄(θ) = ⟨T_θ, φ_θ⟩_θ`, `Ḡ₁(θ) = ⟨φ_θ, φ_θ'⟩_θ`. -/
theorem lemma_5_3
    {X U : Type} [Fintype X] [Fintype U] [DecidableEq X] [DecidableEq U]
    {n m : ℕ} (M : FiniteMDP X U) (π : RSPFamily X U n) (φ : Feat X U n m)
    (N : ℕ) (xstar : X) (ε₀ : ℝ)
    (h21a : Assumption21a π) (h21b : Assumption21b π) (h21c : Assumption21c M π)
    (h21d : Assumption21d M π N xstar ε₀)
    (h31 : Assumption31 π φ) (h32 : Assumption32 M π φ) :
    ∃ L : ℝ, 0 < L ∧ ∃ ε : ℝ, 0 < ε ∧
      ∀ (θ : EuclideanSpace ℝ (Fin n)) (R : Fin 1 ⊕ Fin m → ℝ),
        ε * ∑ i, R i ^ 2 ≤ R ⬝ᵥ (Gbar M π φ (Critic.td1 xstar) L θ).mulVec R := by sorry

end ActorCritic.Finite
