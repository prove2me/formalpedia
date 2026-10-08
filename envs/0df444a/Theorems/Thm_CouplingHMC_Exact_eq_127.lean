-- Prove2me | Theorems.Thm_CouplingHMC_Exact_eq_127
-- name    : CouplingHMC.Exact.eq_127
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T05:28:12.364226+00:00
-- url     : https://prove2.me/theorems/0525c9ff-11b3-4176-b95d-1731f51b88e3
-- title:
--   (127), p. 40 — (1/5)γT inf_{r≤2ℛ} rf′/f ≥ (1/5)γT max(1, 2aℛ)e^{−2aℛ} = (1/5)min(1, T/(4ℛ))max(1, 2ℛ/T)e^{−2ℛ/T} ≥ (1/10)e^{−2ℛ/T}
-- statement:
--   Let $T>0$, $\mathcal R\ge0$, $\gamma=\min(T^{-1},\mathcal R^{-1}/4)$ (equal to $T^{-1}$ if $\mathcal R=0$), $a=T^{-1}$, $R_1=\tfrac52(\mathcal R+T)$ and $f(r)=\int_0^r e^{-a\min(s,R_1)}ds$. Then
--
--   1. for every $0<r\le2\mathcal R$, $\max(1,2a\mathcal R)\,e^{-2a\mathcal R}f(r)\le r e^{-ar}=rf'(r)$; hence $\inf_{r\le2\mathcal R}rf'(r)/f(r)\ge\max(1,2a\mathcal R)e^{-2a\mathcal R}$;
--   2. if $\mathcal R>0$,
--   $$\tfrac15\gamma T\max(1,2a\mathcal R)e^{-2a\mathcal R}=\tfrac15\min\Bigl(1,\frac{T}{4\mathcal R}\Bigr)\max\Bigl(1,\frac{2\mathcal R}{T}\Bigr)e^{-2\mathcal R/T},$$
--   and if $\mathcal R=0$ the left side equals $\tfrac15$;
--   3. $$\tfrac15\gamma T\max(1,2a\mathcal R)e^{-2a\mathcal R}\ge\tfrac1{10}e^{-2\mathcal R/T}.$$
--
--   These are the bounds behind the contraction rate $c_2$ for pairs of points at distance less than $2\mathcal R$.
--
--   **Formalization Note.** Only the inequalities after "$c_2=$" in (127) are stated. The quantity $c_2$ itself is defined through (126), whose constant $-\tfrac15$ the printed argument does not deliver (see the mission description). For $\mathcal R=0$ the paper's $T/(4\mathcal R)$ is $+\infty$, which is why that case is stated separately.
-- source:
--   Bou-Rabee, Eberle, Zimmer, Coupling and convergence for Hamiltonian Monte Carlo, arXiv:1805.00452v2, §5, proof of Theorem 2.4, step (ii), (127), p. 40

import Mathlib
import Definitions.Def_CouplingHMC_Exact_Setting

open MeasureTheory ProbabilityTheory
open scoped ENNReal InnerProductSpace

namespace CouplingHMC.Exact

/-- (127), p. 40, the bounds after `c₂ =`: with `γ`, `a`, `R₁` of (28)–(30),
(a) `max(1, 2aℛ) e^{-2aℛ} f(r) ≤ r f'(r)` for `0 < r ≤ 2ℛ` (so `inf_{r≤2ℛ} r f'(r)/f(r) ≥ max(1, 2aℛ) e^{-2aℛ}`);
(b) `(1/5)γT max(1, 2aℛ) e^{-2aℛ} = (1/5) min(1, T/(4ℛ)) max(1, 2ℛ/T) e^{-2ℛ/T}` for `ℛ > 0`,
    and `= 1/5` for `ℛ = 0` (where `T/(4ℛ) = +∞`);
(c) `(1/5)γT max(1, 2aℛ) e^{-2aℛ} ≥ (1/10) e^{-2ℛ/T}`. -/
theorem eq_127 (T ℛ : ℝ) (hT : 0 < T) (hℛ : 0 ≤ ℛ) :
    (∀ r : ℝ, 0 < r → r ≤ 2 * ℛ →
      max 1 (2 * aC T * ℛ) * Real.exp (-(2 * aC T * ℛ)) * fConc (aC T) (R1C T ℛ) r ≤
        r * Real.exp (-(aC T * r))) ∧
    (0 < ℛ →
      1 / 5 * gammaC T ℛ * T * max 1 (2 * aC T * ℛ) * Real.exp (-(2 * aC T * ℛ)) =
        1 / 5 * min 1 (T / (4 * ℛ)) * max 1 (2 * ℛ / T) * Real.exp (-(2 * ℛ / T))) ∧
    (ℛ = 0 →
      1 / 5 * gammaC T ℛ * T * max 1 (2 * aC T * ℛ) * Real.exp (-(2 * aC T * ℛ)) = 1 / 5) ∧
    1 / 10 * Real.exp (-(2 * ℛ / T)) ≤
      1 / 5 * gammaC T ℛ * T * max 1 (2 * aC T * ℛ) * Real.exp (-(2 * aC T * ℛ)) := by sorry

end CouplingHMC.Exact
