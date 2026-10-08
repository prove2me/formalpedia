-- Prove2me | Theorems.Thm_DeepMFC_FiniteHorizon_theorem_3
-- name    : DeepMFC.FiniteHorizon.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:48:16.657162+00:00
-- url     : https://prove2.me/theorems/ac8db063-f9b2-4543-a457-2f5a960b5d35
-- title:
--   Theorem 3, p. 4070 — inf_𝔸 J ≥ inf over one-hidden-layer networks of J̌^N − O(N^{−1/max(d,4)}√(1+ln N 𝟏_{d=4}) + n_in^{−1/(3(d+1))} + √Δt)
-- statement:
--   Consider the McKean–Vlasov control problem (Problem 1) with data $T,\mu_0,b,\sigma,f,g$ satisfying assumptions (A1)–(A4), (B1)–(B3) and (C1)–(C3), where $\hat\alpha$ is the minimizer (2.6) of the reduced Hamiltonian, $(\mu_t)$ is the flow of marginals of the MKV FBSDE (2.7) and $V$ its decoupling field. Let $\psi$ be a $2\pi$-periodic $\mathcal C^3$ activation function with $\hat\psi_1\ne0$.
--
--   For $N$ agents, $n_{\rm in}$ hidden neurons and $N_T$ time steps of size $\Delta t=T/N_T$, let $\check J^N(\varphi)$ be the cost (2.12) of the discrete-time $N$-agent problem (Problem 2) under a network feedback $\varphi\in\mathbf N^\psi_{d+1,n_{\rm in},k}$. Then
--   $$\inf_{\alpha\in\mathbb A}J(\alpha)\ \ge\ \inf_{\varphi\in\mathbf N^\psi_{d+1,n_{\rm in},k}}\check J^N(\varphi)-\epsilon(N,n_{\rm in},\Delta t),$$
--   where $\epsilon(N,n_{\rm in},\Delta t)=\epsilon_1(N)+\epsilon_2(n_{\rm in})+\epsilon_3(\Delta t)$ with
--   $$\epsilon_1(N)\in O\Big(N^{-1/\max(d,4)}\sqrt{1+\ln(N)\mathbf 1_{\{d=4\}}}\Big),\qquad\epsilon_2(n_{\rm in})\in O\big(n_{\rm in}^{-1/(3(d+1))}\big),\qquad\epsilon_3(\Delta t)\in O\big(\sqrt{\Delta t}\big),$$
--   the constants in the $O(\cdot)$ terms depending only on the data of the problem and on $\psi$.
--
--   The theorem says that minimizing the computable discrete-time, finite-population cost over one-hidden-layer networks, which is what stochastic gradient descent does in practice, comes within an explicit error of the true McKean–Vlasov optimum, with each of the three approximations (finite population, network class, time step) contributing its own rate.
--
--   **Formalization Note.** The three $O(\cdot)$ constants are folded into one constant $C$, chosen after the data and $\psi$ and before $N,n_{\rm in},N_T\ge1$, the probability space and the control. The inequality between infima is stated in the equivalent pointwise form: for every admissible control $\alpha$ on every Problem-1 space, every solution $X$ of (2.2) and every $\eta>0$ there is a network $\varphi\in\mathbf N^\psi_{d+1,n_{\rm in},k}$ with $\check J^N(\varphi)\le J(\alpha)+C\,\mathrm{rate}+\eta$, where $\mathrm{rate}=N^{-1/\max(d,4)}\sqrt{1+\ln(N)\mathbf 1_{\{d=4\}}}+n_{\rm in}^{-1/(3(d+1))}+\sqrt{T/N_T}$. This avoids an infimum of real numbers over a possibly unbounded set. The hypotheses are bundled as `Coeff` (with the derivative witnesses) and `DecouplingField`; see the definitions module for the readings they encode.
-- source:
--   Carmona, Laurière, Convergence analysis of machine learning algorithms for the numerical solution of mean field control and games: II—the finite horizon case, Ann. Appl. Probab. 32(6) (2022), https://doi.org/10.1214/21-AAP1715, p. 4070, Theorem 3

import Mathlib
import Definitions.Def_DeepMFC_FiniteHorizon_Assumptions
import Definitions.Def_DeepMFC_FiniteHorizon_Networks

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace DeepMFC.FiniteHorizon

theorem theorem_3 {d k : ℕ} (M : Model d k) (D : Deriv d k) (hC : Coeff M D)
    (αhat : ℝ → E d → Measure (E d) → E d → Fin k → ℝ) (μflow : ℝ → Measure (E d))
    (V : ℝ → E d → E d) (hD : DecouplingField M D αhat μflow V)
    (ψ : ℝ → ℝ) (hψ : IsActivation ψ) :
    ∃ C : ℝ, ∀ N nin NT : ℕ, 1 ≤ N → 1 ≤ nin → 1 ≤ NT →
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (W : ℝ≥0 → Ω → E d) (X0 : Ω → E d),
        Setting1 M P W X0 →
      ∀ α : ℝ≥0 → Ω → Fin k → ℝ, Admissible M P W X0 α →
      ∀ X : ℝ≥0 → Ω → E d, Solves22 M P W X0 α X →
      ∀ η : ℝ, 0 < η →
      ∃ φ ∈ NN1 ψ (d + 1) nin k,
        Jcheck M N NT (toFeedback φ) ≤ J M P α X
          + C * ((N : ℝ) ^ (-(1 : ℝ) / ((max d 4 : ℕ) : ℝ))
                  * Real.sqrt (1 + Real.log N * (if d = 4 then 1 else 0))
                + (nin : ℝ) ^ (-(1 : ℝ) / (3 * ((d : ℝ) + 1)))
                + Real.sqrt ((M.T : ℝ) / NT))
          + η := by sorry

end DeepMFC.FiniteHorizon
