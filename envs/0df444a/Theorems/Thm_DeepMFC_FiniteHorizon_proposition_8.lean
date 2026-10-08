-- Prove2me | Theorems.Thm_DeepMFC_FiniteHorizon_proposition_8
-- name    : DeepMFC.FiniteHorizon.proposition_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:47:51.428441+00:00
-- url     : https://prove2.me/theorems/4451778d-15ce-43b3-a379-cabacaadfc7e
-- title:
--   Proposition 8, p. 4072 — some network φ̂ ∈ 𝐍^ψ_{d+1,n_in,k} with Lipschitz constants ≤ K₁ has J^N(v̂) ≥ J^N(φ̂) − K₂ n_in^{−1/(3(d+1))}
-- statement:
--   Assume (A1)–(A4), (B1)–(B3), (C1)–(C3), let $\hat v$ be the optimal feedback (3.3), and let $\psi$ be an activation function. There are two positive constants $K_1$ and $K_2$, depending on the data and on $\psi$, such that for every $N\ge1$ and every integer $n_{\rm in}\ge1$ there is a network $\hat\varphi\in\mathbf N^\psi_{d+1,n_{\rm in},k}$ whose Lipschitz constants of $\hat\varphi$, $\partial_x\hat\varphi$ and $\partial^2_{x,x}\hat\varphi$ are bounded by $K_1$, and which satisfies
--   $$J^N(\hat v)\ \ge\ J^N(\hat\varphi)-K_2\,n_{\rm in}^{-1/(3(d+1))}.$$
--
--   This is the second step of Theorem 3: restricting the feedback to one-hidden-layer networks costs at most $K_2n_{\rm in}^{-1/(3(d+1))}$, and the network keeps uniformly bounded regularity, which the time-discretization step needs.
--
--   **Formalization Note.** $J^N(\hat v)$ and $J^N(\hat\varphi)$ are computed on any common Problem-3 space for $N$ agents and any solutions of (3.2). The network is a feedback of $(t,x)$; its Lipschitz constants are for functions of $(t,x)$ on $\mathbb R\times\mathbb R^d$. $K_1,K_2$ are chosen before $N$ and $n_{\rm in}$; $\hat\varphi$ may depend on $N$ and $n_{\rm in}$.
-- source:
--   Carmona, Laurière, Convergence analysis of machine learning algorithms for the numerical solution of mean field control and games: II—the finite horizon case, Ann. Appl. Probab. 32(6) (2022), https://doi.org/10.1214/21-AAP1715, p. 4072, Proposition 8

import Mathlib
import Definitions.Def_DeepMFC_FiniteHorizon_Assumptions
import Definitions.Def_DeepMFC_FiniteHorizon_Networks

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace DeepMFC.FiniteHorizon

theorem proposition_8 {d k : ℕ} (M : Model d k) (D : Deriv d k) (hC : Coeff M D)
    (αhat : ℝ → E d → Measure (E d) → E d → Fin k → ℝ) (μflow : ℝ → Measure (E d))
    (V : ℝ → E d → E d) (hD : DecouplingField M D αhat μflow V)
    (ψ : ℝ → ℝ) (hψ : IsActivation ψ) :
    ∃ K₁ K₂ : ℝ, 0 < K₁ ∧ 0 < K₂ ∧ ∀ N : ℕ, 1 ≤ N → ∀ nin : ℕ, 1 ≤ nin →
      ∃ φhat ∈ NN1 ψ (d + 1) nin k, NetLip K₁ (toFeedback φhat) ∧
        ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (W : Fin N → ℝ≥0 → Ω → E d)
          (X0 : Fin N → Ω → E d), Setting3 M P W X0 →
        ∀ Xv Xφ : Fin N → ℝ≥0 → Ω → E d, Solves32 M P W X0 (vhat αhat μflow V) Xv →
          Solves32 M P W X0 (toFeedback φhat) Xφ →
          JN M P (toFeedback φhat) Xφ - K₂ * (nin : ℝ) ^ (-(1 : ℝ) / (3 * ((d : ℝ) + 1)))
            ≤ JN M P (vhat αhat μflow V) Xv := by sorry

end DeepMFC.FiniteHorizon
