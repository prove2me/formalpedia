-- Prove2me | Theorems.Thm_ActorCritic_Finite_lemma_5_6
-- name    : ActorCritic.Finite.lemma_5_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T02:16:41.14203+00:00
-- url     : https://prove2.me/theorems/c2eafd77-4e3c-49be-9fbf-a6ce34ec79c8
-- title:
--   Lemma 5.6 — TD(λ): R'Ḡ(θ)R ≥ ε|R|² uniformly in θ, for some L and ε > 0
-- statement:
--   Let a finite cost MDP, a policy family $\mu_\theta$ and critic features $\phi_\theta$ satisfy Assumptions 2.1 (with data $N$, $x^*$, $\epsilon_0$), 3.1 and 3.2, and fix $\lambda\in(0,1)$. For the TD($\lambda$) critic let $\bar G(\theta)=\begin{pmatrix}1&0\\ \bar Z(\theta)/L&\bar G_1(\theta)\end{pmatrix}$ with
--   $$
--   \bar Z(\theta)=(1-\lambda)^{-1}\langle\underline1,\phi_\theta\rangle_\theta,\qquad \bar G_1(\theta)=\langle\phi_\theta,\phi_\theta'\rangle_\theta-(1-\lambda)\sum_{k=0}^\infty\lambda^k\langle P_\theta^{k+1}\phi_\theta,\phi_\theta'\rangle_\theta .
--   $$
--   Then there exist $L>0$ and $\epsilon>0$ such that for all $\theta\in\mathbb R^n$ and $R\in\mathbb R^{m+1}$,
--   $$
--   R'\bar G(\theta)R\ge\epsilon|R|^2 .
--   $$
--
--   This is the TD($\lambda$) counterpart of Lemma 5.3, the stability hypothesis for the TD($\lambda$) critic.
--
--   **Formalization Note** $L$ and $\epsilon$ may depend on $\lambda$ (the lemma is stated in §5.2 for a fixed $\lambda$) but not on $\theta$ or $R$. $|R|^2=\sum_iR_i^2$ on `Fin 1 ⊕ Fin m`. The orientation of $\langle P_\theta^{k+1}\phi_\theta,\phi_\theta'\rangle_\theta$ is fixed in the definitions module; the quadratic form $R'\bar G(\theta)R$ does not depend on it.
-- source:
--   Konda and Tsitsiklis, On Actor-Critic Algorithms, SIAM J. Control Optim. 42 (2003), p. 1161, Lemma 5.6 (h̄, Ḡ, Ḡ₁, Z̄ on pp. 1159–1160)

import Mathlib
import Definitions.Def_ActorCritic_Finite_SteadyState

namespace ActorCritic.Finite

/-- **Lemma 5.6** (Konda–Tsitsiklis 2003, p. 1161), TD(λ) critic, `0 < λ < 1`, finite case.
Under Assumptions 2.1 (data `N`, `x*`, `ε₀`), 3.1 and 3.2, for each `λ ∈ (0, 1)` there exist
`L > 0` and `ε > 0` such that for all `θ ∈ ℝⁿ` and `R ∈ ℝ^{1+m}`, `R' Ḡ(θ) R ≥ ε |R|²`, where
`Ḡ(θ) = [[1, 0], [Z̄(θ)/L, Ḡ₁(θ)]]` with the TD(λ) quantities `Z̄(θ) = (1 − λ)^{-1}⟨1, φ_θ⟩_θ`,
`Ḡ₁(θ) = ⟨φ_θ, φ_θ'⟩_θ − (1 − λ) ∑_k λ^k ⟨P_θ^{k+1} φ_θ, φ_θ'⟩_θ`. -/
theorem lemma_5_6
    {X U : Type} [Fintype X] [Fintype U] [DecidableEq X] [DecidableEq U]
    {n m : ℕ} (M : FiniteMDP X U) (π : RSPFamily X U n) (φ : Feat X U n m)
    (N : ℕ) (xstar : X) (ε₀ : ℝ)
    (h21a : Assumption21a π) (h21b : Assumption21b π) (h21c : Assumption21c M π)
    (h21d : Assumption21d M π N xstar ε₀)
    (h31 : Assumption31 π φ) (h32 : Assumption32 M π φ) :
    ∀ lam : ℝ, 0 < lam → lam < 1 →
      ∃ L : ℝ, 0 < L ∧ ∃ ε : ℝ, 0 < ε ∧
        ∀ (θ : EuclideanSpace ℝ (Fin n)) (R : Fin 1 ⊕ Fin m → ℝ),
          ε * ∑ i, R i ^ 2 ≤ R ⬝ᵥ (Gbar M π φ (Critic.tdLambda lam) L θ).mulVec R := by sorry

end ActorCritic.Finite
