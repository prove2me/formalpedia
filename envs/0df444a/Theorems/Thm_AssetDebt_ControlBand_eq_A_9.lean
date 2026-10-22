-- Prove2me | Theorems.Thm_AssetDebt_ControlBand_eq_A_9
-- name    : AssetDebt.ControlBand.eq_A_9
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:14:04.640556+00:00
-- url     : https://prove2.me/theorems/c7054e86-f040-4cda-9b4c-f9db0b9a0830
-- title:
--   (A.9), proof of Proposition 4, Online Appendix p. 7 — before the first sale, $V_t = \max\{\rho E_t V_{t+1}, R^o_t(1 - \rho^{m-t}d_m/p_t), p_t - \rho^{m-t}d_m\}$
-- statement:
--   Assume no capacity constraint ($\ell = 1$) and a single debt payment $D \ge 0$ due at the end of period $m$, with $1 \le m < T$. Fix a period $1 \le t \le m$ and a price $p > 0$, consider the state in which no asset has been sold yet ($x = 1$, $w = 0$), and write $\delta = \rho^{m-t} D$ and $C_t = \rho E_t V_{t+1}(1, 0, P_{t+1}; d)$ (with $C_m = 0$). Then
--
--   $$V_t(1, 0, p; d) = \max\big\{ C_t,\ \ R^o_t(1 - \delta/p),\ \ p - \delta \big\},$$
--
--   and the three terms are objective values of three quantities:
--
--   1. for $t < m$, selling nothing gives the objective value $C_t$;
--   2. if $\delta \le p$, selling $q = \delta/p$ gives the objective value $R^o_t(1 - \delta/p)$;
--   3. if $\delta \le p$, selling the entire asset gives the objective value $p - \delta$.
--
--   This is the closed form on which the control band of Proposition 4 rests.
--
--   **Formalization Note** The objective is that of eq. (2) at $t = m$ and of eq. (3) at $t < m$, evaluated off the feasible set as well. At $t = m$ selling nothing is infeasible when $D > 0$, so clause 1 is stated for $t < m$ only; the value identity covers $t = m$, as the paper remarks.
-- source:
--   Ahn, Wang & Wu, Asset Selling Under Debt Obligations, SSRN 3472345 (version of May 7, 2019), Online Appendix p. 7 (PDF 39), proof of Proposition 4, eq. (A.9)

import Mathlib
import Definitions.Def_AssetDebt_ControlBand_Model

namespace AssetDebt.ControlBand

open MeasureTheory ProbabilityTheory

/-- (A.9), proof of Proposition 4, Online Appendix p. 7: under a single payment `d_m = D` at
`m < T` and `ℓ = 1`, when no asset is sold before period `t ≤ m` (state `x = 1`, `w = 0`),
with `δ = ρ^{m-t} d_m`,
`V_t = max{ρ E_t V_{t+1}, R^o_t (1 - δ/p), p - δ}`, where the three terms are the objective
values of selling nothing (`t < m`), selling `δ/p`, and selling the entire asset. -/
theorem eq_A_9 (P : Params) (hS : P.Standing) (hℓ : P.ℓ = 1)
    (m : ℕ) (hm : 1 ≤ m ∧ m < P.T) (D : ℝ) (hD : 0 ≤ D) (t : ℕ) (ht : 1 ≤ t ∧ t ≤ m)
    (p : ℝ) (hp : 0 < p) :
    V P (singlePayment m D) m t 1 0 p =
        max (max (C P m D t p) (Ro P t p * (1 - P.ρ ^ (m - t) * D / p))) (p - P.ρ ^ (m - t) * D) ∧
    (t < m → objV P (singlePayment m D) m t 1 0 p 0 = C P m D t p) ∧
    (P.ρ ^ (m - t) * D ≤ p →
        objV P (singlePayment m D) m t 1 0 p (P.ρ ^ (m - t) * D / p) =
          Ro P t p * (1 - P.ρ ^ (m - t) * D / p)) ∧
    (P.ρ ^ (m - t) * D ≤ p →
        objV P (singlePayment m D) m t 1 0 p 1 = p - P.ρ ^ (m - t) * D) := by sorry

end AssetDebt.ControlBand
