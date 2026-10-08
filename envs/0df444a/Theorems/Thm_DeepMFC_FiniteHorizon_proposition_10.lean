-- Prove2me | Theorems.Thm_DeepMFC_FiniteHorizon_proposition_10
-- name    : DeepMFC.FiniteHorizon.proposition_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:47:55.066979+00:00
-- url     : https://prove2.me/theorems/02cb7997-0e43-4b29-bb37-d35ad1102b8c
-- title:
--   Proposition 10, pp. 4073–4074 — a one-hidden-layer network φ_𝔣 approximates 𝔣 ∈ 𝒞(R, K, L₁, L₂, L₃) within C(1+R)n_in^{−1/(2(d+1))}, with controlled Lipschitz constants
-- statement:
--   Fix $d$. There is an integer $n_0$ (depending only on $d$ and the absolute constant of the trigonometric approximation theorem) with the following property. Let $k$ be the output dimension, $T>0$, $\psi$ an activation function ($2\pi$-periodic, $\mathcal C^3$, $\hat\psi_1\ne0$), and $K,L_1,L_2,L_3>0$. Then there is a constant $C$, depending only on these and on $d,k,T,\psi$, such that for every $R>0$, every $\mathfrak f\in\mathcal C(R,K,L_1,L_2,L_3)$ and every integer $n_{\rm in}>n_0$ there is a one-hidden-layer network $\varphi_{\mathfrak f}\in\mathbf N^\psi_{d+1,n_{\rm in},k}$ with
--   $$\|\mathfrak f-\varphi_{\mathfrak f}\|_{\mathcal C^0([0,T]\times\bar B_d(0,R);\mathbb R^k)}\le C(1+R)\,n_{\rm in}^{-1/(2(d+1))},$$
--   and such that the Lipschitz constants of $\varphi_{\mathfrak f}$, $\partial_x\varphi_{\mathfrak f}$ and $\partial^2_{x,x}\varphi_{\mathfrak f}$ are at most $C\big(1+R\,n_{\rm in}^{-1/(2(d+1))}\big)$. The constant $C$ does not depend on $R$.
--
--   This is the approximation result that turns the Lipschitz optimal feedback into a neural network without losing control of its regularity.
--
--   **Formalization Note.** The sup-norm bound is stated pointwise on $[0,T]\times\bar B_d(0,R)$. The Lipschitz constants are for functions of $(t,x)$ on all of $\mathbb R\times\mathbb R^d$ (the network is built from a periodic function whose derivatives are controlled on the whole torus). The quantifier order is the page's: $n_0$ depends on $d$ only; $C$ is chosen after $k,T,\psi,K,L_1,L_2,L_3$ and before $R$, $\mathfrak f$, $n_{\rm in}$.
-- source:
--   Carmona, Laurière, Convergence analysis of machine learning algorithms for the numerical solution of mean field control and games: II—the finite horizon case, Ann. Appl. Probab. 32(6) (2022), https://doi.org/10.1214/21-AAP1715, pp. 4073–4074, Proposition 10

import Mathlib
import Definitions.Def_DeepMFC_FiniteHorizon_Networks

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace DeepMFC.FiniteHorizon

theorem proposition_10 (d : ℕ) :
    ∃ n₀ : ℕ, ∀ (k : ℕ) (T : ℝ), 0 < T → ∀ ψ : ℝ → ℝ, IsActivation ψ →
      ∀ K L₁ L₂ L₃ : ℝ, 0 < K → 0 < L₁ → 0 < L₂ → 0 < L₃ →
      ∃ C : ℝ, ∀ R : ℝ, 0 < R → ∀ 𝔣 : ℝ → E d → Fin k → ℝ, InClassC T R K L₁ L₂ L₃ 𝔣 →
      ∀ nin : ℕ, n₀ < nin →
      ∃ φ ∈ NN1 ψ (d + 1) nin k,
        (∀ t ∈ Set.Icc 0 T, ∀ x ∈ Metric.closedBall (0 : E d) R,
          ‖𝔣 t x - toFeedback φ t x‖ ≤ C * (1 + R) * (nin : ℝ) ^ (-(1 : ℝ) / (2 * ((d : ℝ) + 1)))) ∧
        NetLip (C * (1 + R * (nin : ℝ) ^ (-(1 : ℝ) / (2 * ((d : ℝ) + 1))))) (toFeedback φ) := by sorry

end DeepMFC.FiniteHorizon
