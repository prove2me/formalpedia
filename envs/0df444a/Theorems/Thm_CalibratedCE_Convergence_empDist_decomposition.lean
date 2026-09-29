-- Prove2me | Theorems.Thm_CalibratedCE_Convergence_empDist_decomposition
-- name    : CalibratedCE.Convergence.empDist_decomposition
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T13:30:32.061391+00:00
-- url     : https://prove2.me/theorems/6e631fd4-5129-42e8-b9a4-23c76755feb2
-- title:
--   Proof of Theorem 1 (p. 45): decomposition of $D_t(x,y)$ into a forecast term and a calibration error
-- statement:
--   Let player 1 issue forecasts $f(s)$ (vectors in $\mathbb{R}^n$) and play $x(s) = R_1(f(s))$ in round $s$, for some function $R_1$ from forecasts to $S(1)$, and let $y(s) \in S(2)$ be player 2's plays. Fix $t \in \mathbb{N}$, $a \in S(1)$, $b \in S(2)$, and let $P_t(a)$ be the set of forecasts issued in the first $t$ rounds at which player 1 plays $a$, i.e. the forecasts in $M_p(a)$ actually used. With $N(p, t)$ and $\rho(p, b, t)$ as in the definition of calibration,
--   $$\begin{aligned} D_t(a, b) &= t^{-1} \sum_{p \in P_t(a)} |\{ r < t : f(r) = p,\ y(r) = b \}| \\ &= t^{-1} \sum_{p \in P_t(a)} \rho(p, b, t)\, N(p, t) \\ &= t^{-1} \sum_{p \in P_t(a)} p_b\, N(p, t) + t^{-1} \sum_{p \in P_t(a)} \big(\rho(p, b, t) - p_b\big) N(p, t). \end{aligned}$$
--
--   The first term is what the forecasts predict; the second is controlled by calibration. The identity needs no calibration or best-reply hypothesis.
--
--   **Formalization Note** The paper writes the sums over $p \in M_p(x)$; only the issued forecasts contribute, so the sums run over them. At $t = 0$ both sides are $0$ by the convention $0^{-1} = 0$. The paper's first display line, the sum of $\chi(y, r)$ over rounds with $f(r) \in M_p(x)$, is the definition of $D_t$ and is not restated.
-- source:
--   Foster and Vohra, Calibrated learning and correlated equilibrium, Games Econ. Behav. 21 (1997), p. 45, proof of Theorem 1 (display)

import Mathlib
import Definitions.Def_CalibratedCE_Shared_Calibration
import Definitions.Def_CalibratedCE_Convergence_EmpDist

namespace CalibratedCE.Convergence

/-- Proof of Theorem 1, p. 45, the decomposition display: when player 1 plays `R₁ (f₁ s)` in
round `s`, the empirical frequency of `(a, b)` splits into a forecast-weighted main term and a
calibration error term. The sums run over the forecasts issued in the first `t` rounds at
which player 1 plays `a`. -/
theorem empDist_decomposition {m n : ℕ} (R₁ : (Fin n → ℝ) → Fin m) (f₁ : ℕ → Fin n → ℝ)
    (y : ℕ → Fin n) (t : ℕ) (a : Fin m) (b : Fin n) :
    empDist (fun s => R₁ (f₁ s)) y t a b =
        (t : ℝ)⁻¹ * ∑ p ∈ ((Finset.range t).image f₁).filter (fun p => R₁ p = a),
          (((Finset.range t).filter (fun r => f₁ r = p ∧ y r = b)).card : ℝ) ∧
    empDist (fun s => R₁ (f₁ s)) y t a b =
        (t : ℝ)⁻¹ * ∑ p ∈ ((Finset.range t).image f₁).filter (fun p => R₁ p = a),
          Shared.rho f₁ y p b t * (Shared.N f₁ p t : ℝ) ∧
    empDist (fun s => R₁ (f₁ s)) y t a b =
        (t : ℝ)⁻¹ * ∑ p ∈ ((Finset.range t).image f₁).filter (fun p => R₁ p = a),
          p b * (Shared.N f₁ p t : ℝ) +
        (t : ℝ)⁻¹ * ∑ p ∈ ((Finset.range t).image f₁).filter (fun p => R₁ p = a),
          (Shared.rho f₁ y p b t - p b) * (Shared.N f₁ p t : ℝ) := by sorry

end CalibratedCE.Convergence
