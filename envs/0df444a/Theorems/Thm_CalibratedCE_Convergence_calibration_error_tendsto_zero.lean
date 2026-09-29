-- Prove2me | Theorems.Thm_CalibratedCE_Convergence_calibration_error_tendsto_zero
-- name    : CalibratedCE.Convergence.calibration_error_tendsto_zero
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T13:31:22.264217+00:00
-- url     : https://prove2.me/theorems/a91eb3bc-d051-4f54-b7af-5d8bff263416
-- title:
--   Proof of Theorem 1 (p. 45): calibration makes the error term vanish
-- statement:
--   Let player 1 issue forecasts $f(s) \in \mathbb{R}^n$ and play $R_1(f(s))$, and let $y(s) \in S(2)$ be player 2's plays. Suppose $f$ is calibrated with respect to $y$. Then for every $a \in S(1)$ and $b \in S(2)$,
--   $$\lim_{t \to \infty} \; t^{-1} \sum_{p \in P_t(a)} \big(\rho(p, b, t) - p_b\big) N(p, t) = 0,$$
--   where $P_t(a)$ is the set of forecasts issued in the first $t$ rounds at which $R_1$ selects $a$.
--
--   This is the second term of the decomposition of $D_t(a, b)$; its vanishing is where calibration enters the proof of Theorem 1.
--
--   **Formalization Note** The paper takes the limit along a subsequence $t_i$; the statement here is along all $t$, which implies it.
-- source:
--   Foster and Vohra, Calibrated learning and correlated equilibrium, Games Econ. Behav. 21 (1997), p. 45, proof of Theorem 1

import Mathlib
import Definitions.Def_CalibratedCE_Shared_Calibration

open Filter Topology

namespace CalibratedCE.Convergence

/-- Proof of Theorem 1, p. 45: if player 1's forecasts are calibrated against player 2's plays,
the calibration error term of the decomposition display tends to `0`. -/
theorem calibration_error_tendsto_zero {m n : ℕ} (R₁ : (Fin n → ℝ) → Fin m)
    (f₁ : ℕ → Fin n → ℝ) (y : ℕ → Fin n) (hcal : Shared.Calibrated f₁ y) (a : Fin m) (b : Fin n) :
    Tendsto (fun t : ℕ => (t : ℝ)⁻¹ *
        ∑ p ∈ ((Finset.range t).image f₁).filter (fun p => R₁ p = a),
          (Shared.rho f₁ y p b t - p b) * (Shared.N f₁ p t : ℝ)) atTop (𝓝 0) := by sorry

end CalibratedCE.Convergence
